-- Prove2me | solution 1 for ThresholdTheorem.zero_level_block_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T12:57:39.075419+00:00
-- url     : https://prove2.me/submissions/8ab784f6-7b46-46e9-a5f2-eac9faa48723

import Mathlib
import Theorems.Thm_ThresholdTheorem_noisy_tv_le_fault_rate_mul_size

open Matrix

namespace ThresholdTheorem

/-! ## The equivalence `Fin n ≃ Fin n × Fin 1` -/

def finProdOneEquiv (n : ℕ) : Fin n ≃ Fin n × Fin 1 where
  toFun i := (i, 0)
  invFun q := q.1
  left_inv i := rfl
  right_inv q := by
    rcases q with ⟨i, j⟩
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    rfl

/-! ## Transport of locations/layers/circuits -/

variable {Q Q' : Type*}

def pushEmbedding (e : Q ≃ Q') {k : ℕ} (s : Fin k ↪ Q) : Fin k ↪ Q' :=
  ⟨fun i => e (s i), fun i j h => s.injective (e.injective h)⟩

def mapLocation (e : Q ≃ Q') (ℓ : Location Q) : Location Q' :=
  ⟨ℓ.op, pushEmbedding e ℓ.support⟩

lemma list_ofFn_pushEmbedding (e : Q ≃ Q') {k : ℕ} (s : Fin k ↪ Q) :
    List.ofFn (pushEmbedding e s) = (List.ofFn s).map e := by
  change List.ofFn (fun i => e (s i)) = (List.ofFn (s : Fin k → Q)).map e
  exact List.ofFn_comp' _ _

lemma flatMap_ofFn_support_map (e : Q ≃ Q') (locs : List (Location Q)) :
    (locs.map (mapLocation e)).flatMap (fun ℓ => List.ofFn ℓ.support) =
      (locs.flatMap (fun ℓ => List.ofFn ℓ.support)).map e := by
  induction locs with
  | nil => simp
  | cons ℓ locs ih =>
      simp [mapLocation, List.flatMap_cons, List.map_append,
        list_ofFn_pushEmbedding, ih]

lemma list_count_map_equiv [DecidableEq Q] [DecidableEq Q']
    (e : Q ≃ Q') (l : List Q) (b : Q') :
    (l.map e).count b = l.count (e.symm b) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a = e.symm b
      · have hb : e a = b := by
          rw [h]
          exact e.apply_symm_apply b
        simp [h, hb, ih]
      · have hb : e a ≠ b := by
          intro hb
          apply h
          calc
            a = e.symm (e a) := (e.symm_apply_apply a).symm
            _ = e.symm b := by rw [hb]
        simp [h, hb, ih]

def mapLayer [DecidableEq Q] [DecidableEq Q'] (e : Q ≃ Q') (L : Layer Q) :
    Layer Q' where
  locs := L.locs.map (mapLocation e)
  partition := by
    intro q'
    rw [flatMap_ofFn_support_map e]
    rw [list_count_map_equiv e]
    exact L.partition (e.symm q')

def mapCircuit [DecidableEq Q] [DecidableEq Q'] (e : Q ≃ Q') (C : Circuit Q) :
    Circuit Q' :=
  C.map (mapLayer e)

lemma size_mapCircuit [DecidableEq Q] [DecidableEq Q'] (e : Q ≃ Q')
    (C : Circuit Q) :
    (mapCircuit e C).size = C.size := by
  simp [mapCircuit, Circuit.size, mapLayer, List.map_map, Function.comp_def]

/-! ## Reindexing operators -/

noncomputable def pushOp (e : Q ≃ Q') (ρ : Op Q) : Op Q' :=
  fun x y => ρ (fun q => x (e q)) (fun q => y (e q))

@[simp] lemma pushOp_zero (e : Q ≃ Q') :
    pushOp e (0 : Op Q) = 0 := by
  funext x y
  simp [pushOp]

lemma pushOp_add (e : Q ≃ Q') (A B : Op Q) :
    pushOp e (A + B) = pushOp e A + pushOp e B := by
  funext x y
  simp [pushOp]

lemma pushOp_smul (e : Q ≃ Q') (a : ℂ) (A : Op Q) :
    pushOp e (a • A) = a • pushOp e A := by
  funext x y
  simp [pushOp]

lemma pushOp_smul_real (e : Q ≃ Q') (a : ℝ) (A : Op Q) :
    pushOp e (a • A) = a • pushOp e A := by
  funext x y
  simp [pushOp]

lemma pushOp_list_sum (e : Q ≃ Q') (l : List (Op Q)) :
    pushOp e l.sum = (l.map (pushOp e)).sum := by
  induction l with
  | nil => simp
  | cons A l ih =>
      simp [List.sum_cons, pushOp_add, ih]

lemma sum_reindex_bitstrings {M : Type*} [AddCommMonoid M]
    [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] (e : Q ≃ Q') (f : (Q → Fin 2) → M) :
    (∑ z' : Q' → Fin 2, f (fun q => z' (e q))) =
      ∑ z : Q → Fin 2, f z := by
  let E : (Q' → Fin 2) ≃ (Q → Fin 2) :=
    { toFun := fun z' q => z' (e q)
      invFun := fun z q' => z (e.symm q')
      left_inv := by
        intro z'
        funext q
        simp
      right_inv := by
        intro z
        funext q'
        simp }
  simpa [E] using Equiv.sum_comp E f

lemma pushOp_mul [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] (e : Q ≃ Q') (A B : Op Q) :
    pushOp e (A * B) = pushOp e A * pushOp e B := by
  funext x y
  simp only [pushOp, Matrix.mul_apply]
  exact (sum_reindex_bitstrings e
    (fun z : Q → Fin 2 =>
      A (fun q => x (e q)) z * B z (fun q => y (e q)))).symm

lemma pushOp_star (e : Q ≃ Q') (A : Op Q) :
    pushOp e Aᴴ = (pushOp e A)ᴴ := by
  funext x y
  simp [pushOp, Matrix.conjTranspose]

lemma pushOp_liftOp {k : ℕ} (e : Q ≃ Q') (s : Fin k ↪ Q) (A : QMat k) :
    pushOp e (liftOp s A) = liftOp (pushEmbedding e s) A := by
  classical
  funext x y
  simp only [pushOp, liftOp, pushEmbedding]
  have hiff :
      (∀ q : Q, q ∉ Set.range s → x (e q) = y (e q)) ↔
        (∀ q' : Q', q' ∉ Set.range (fun i : Fin k => e (s i)) → x q' = y q') := by
    constructor
    · intro h q' hq'
      have hq : e.symm q' ∉ Set.range s := by
        intro hmem
        rcases hmem with ⟨i, hi⟩
        apply hq'
        exact ⟨i, by
          calc
            e (s i) = e (e.symm q') := by rw [hi]
            _ = q' := e.apply_symm_apply q'⟩
      have := h (e.symm q') hq
      simpa using this
    · intro h q hq
      have hq' : e q ∉ Set.range (fun i : Fin k => e (s i)) := by
        intro hmem
        rcases hmem with ⟨i, hi⟩
        have : s i = q := e.injective hi
        exact hq ⟨i, this⟩
      have := h (e q) hq'
      simpa using this
  simp only [hiff]
  rfl

lemma pushOp_applyKraus [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {k : ℕ}
    (e : Q ≃ Q') (s : Fin k ↪ Q) (K : List (QMat k)) (ρ : Op Q) :
    pushOp e (applyKraus s K ρ) =
      applyKraus (pushEmbedding e s) K (pushOp e ρ) := by
  classical
  simp only [applyKraus]
  rw [pushOp_list_sum]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro A hA
  simp only [Function.comp_apply]
  calc
    pushOp e (liftOp s A * ρ * (liftOp s A)ᴴ)
        = pushOp e (liftOp s A * ρ) * pushOp e ((liftOp s A)ᴴ) := by
          rw [pushOp_mul]
    _ = (pushOp e (liftOp s A) * pushOp e ρ) *
          pushOp e ((liftOp s A)ᴴ) := by
          rw [pushOp_mul]
    _ = (liftOp (pushEmbedding e s) A * pushOp e ρ) *
          (liftOp (pushEmbedding e s) A)ᴴ := by
          rw [pushOp_liftOp, pushOp_star, pushOp_liftOp]

/-! ## Noisy layers and states -/

noncomputable def noisyStep {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ}
    (N : NoiseModel p) (t : ℕ) (σ : Op Q) (ℓ : Location Q) (j : ℕ) : Op Q :=
  (1 - N.prob t j) • applyKraus ℓ.support ℓ.op.idealKraus σ +
    N.prob t j • applyKraus ℓ.support (N.fault t j ℓ.op.arity).kraus σ

lemma pushOp_noisyStep [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {p : ℝ} (N : NoiseModel p)
    (t : ℕ) (e : Q ≃ Q') (σ : Op Q) (ℓ : Location Q) (j : ℕ) :
    pushOp e (noisyStep N t σ ℓ j) =
      noisyStep N t (pushOp e σ) (mapLocation e ℓ) j := by
  simp only [noisyStep, pushOp_add, pushOp_smul_real, pushOp_applyKraus]
  rfl

lemma zipIdx_map {α β : Type*} (f : α → β) (l : List α) :
    (l.map f).zipIdx =
      (l.zipIdx).map (fun p : α × ℕ => (f p.1, p.2)) := by
  exact List.zipIdx_map (l := l) (k := 0) (f := f)

lemma foldl_zipIdx_noisy_map [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {p : ℝ}
    (N : NoiseModel p) (t : ℕ) (e : Q ≃ Q')
    (l : List (Location Q × ℕ)) (ρ : Op Q) :
    l.foldl (fun σ p => noisyStep N t σ (mapLocation e p.1) p.2)
        (pushOp e ρ) =
      pushOp e (l.foldl (fun σ p => noisyStep N t σ p.1 p.2) ρ) := by
  induction l generalizing ρ with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [← pushOp_noisyStep]
      exact ih _

lemma pushOp_noisyLayer [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {p : ℝ}
    (N : NoiseModel p) (t : ℕ) (e : Q ≃ Q') (L : Layer Q) (ρ : Op Q) :
    pushOp e (noisyLayer N t L ρ) =
      noisyLayer N t (mapLayer e L) (pushOp e ρ) := by
  simp only [noisyLayer, mapLayer]
  rw [zipIdx_map (mapLocation e)]
  rw [List.foldl_map]
  exact (foldl_zipIdx_noisy_map N t e L.locs.zipIdx ρ).symm

lemma pushOp_initState (e : Q ≃ Q') :
    pushOp e (initState Q) = initState Q' := by
  funext x y
  simp only [pushOp, initState]
  have hx : (fun q : Q => x (e q)) = 0 ↔ x = 0 := by
    constructor
    · intro h
      funext q'
      have := congrFun h (e.symm q')
      simpa using this
    · intro h
      funext q
      simp [h]
  have hy : (fun q : Q => y (e q)) = 0 ↔ y = 0 := by
    constructor
    · intro h
      funext q'
      have := congrFun h (e.symm q')
      simpa using this
    · intro h
      funext q
      simp [h]
  rw [hx, hy]

lemma foldl_noisyState_map [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {p : ℝ}
    (N : NoiseModel p) (e : Q ≃ Q') (l : List (Layer Q × ℕ)) (ρ : Op Q) :
    l.foldl (fun σ p => noisyLayer N p.2 (mapLayer e p.1) σ) (pushOp e ρ) =
      pushOp e (l.foldl (fun σ p => noisyLayer N p.2 p.1 σ) ρ) := by
  induction l generalizing ρ with
  | nil => simp
  | cons p ps ih =>
      simp only [List.foldl_cons]
      rw [← pushOp_noisyLayer]
      exact ih _

lemma pushOp_noisyState [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q'] {p : ℝ}
    (N : NoiseModel p) (e : Q ≃ Q') (C : Circuit Q) :
    pushOp e (noisyState N C) = noisyState N (mapCircuit e C) := by
  simp only [noisyState, mapCircuit]
  rw [zipIdx_map (mapLayer e)]
  rw [List.foldl_map]
  rw [← pushOp_initState e]
  exact (foldl_noisyState_map N e C.zipIdx (initState Q)).symm

lemma outDist_pushOp (e : Q ≃ Q') (ρ : Op Q) (x : Q' → Fin 2) :
    outDist (pushOp e ρ) x = outDist ρ (fun q => x (e q)) := rfl

/-! ## Decoding for `b = 1` -/

lemma decodeDist_fin_one {n : ℕ}
    (P : (Fin n × Fin 1 → Fin 2) → ℝ) :
    decodeDist (fun x : Fin 1 → Fin 2 => x 0) P =
      fun y : Fin n → Fin 2 => P (fun q : Fin n × Fin 1 => y q.1) := by
  classical
  funext y
  unfold decodeDist
  let x0 : Fin n × Fin 1 → Fin 2 := fun q => y q.1
  have hx0 : x0 ∈ Finset.univ.filter
      (fun x : Fin n × Fin 1 → Fin 2 => (fun i => x (i, 0)) = y) := by
    simp [x0]
  rw [Finset.sum_eq_single x0]
  · intro x hx hne
    exfalso
    apply hne
    have hxy : (fun i => x (i, 0)) = y := (Finset.mem_filter.mp hx).2
    funext q
    rcases q with ⟨i, j⟩
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    exact congrFun hxy i
  · intro hx
    exact (hx hx0).elim

lemma decodeDist_outDist_noisy_map {n : ℕ} {p : ℝ}
    (N : NoiseModel p) (C : Circuit (Fin n)) :
    decodeDist (fun x : Fin 1 → Fin 2 => x 0)
        (outDist (noisyState N (mapCircuit (finProdOneEquiv n) C))) =
      outDist (noisyState N C) := by
  funext y
  rw [decodeDist_fin_one]
  rw [← pushOp_noisyState N (finProdOneEquiv n) C]
  dsimp only
  rw [outDist_pushOp]
  rfl

end ThresholdTheorem

open ThresholdTheorem

/-! ## Final theorem -/

theorem solution :
    ∀ c : ℝ, 1 ≤ c →
      ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
        ∀ (n : ℕ) (C : Circuit (Fin n)),
          ∃ C' : Circuit (Fin n × Fin b),
            (C'.size : ℝ) ≤ C.size ∧
            ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
              tvDist (decodeDist dec (outDist (noisyState N C')))
                (outDist (idealState C)) ≤ p * C.size := by
  intro c hc
  refine ⟨1, (fun x : Fin 1 → Fin 2 => x 0), ?_⟩
  intro n C
  let e : Fin n ≃ Fin n × Fin 1 := finProdOneEquiv n
  let C' : Circuit (Fin n × Fin 1) := mapCircuit e C
  refine ⟨C', ?_, ?_⟩
  · have hsize : C'.size = C.size := size_mapCircuit e C
    rw [hsize]
  · intro p hp hlt N
    have hp_le_one : p ≤ 1 := by
      have h1 : p ≤ c * p := by
        simpa using (mul_le_mul_of_nonneg_right hc hp)
      linarith
    have hdecode :
        decodeDist (fun x : Fin 1 → Fin 2 => x 0)
            (outDist (noisyState N C')) =
          outDist (noisyState N C) := by
      simpa [C', e] using decodeDist_outDist_noisy_map N C
    rw [hdecode]
    exact noisy_tv_le_fault_rate_mul_size C p hp_le_one N

