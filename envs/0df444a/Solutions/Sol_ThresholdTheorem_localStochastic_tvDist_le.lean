-- Prove2me | solution 1 for ThresholdTheorem.localStochastic_tvDist_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:41:49.580788+00:00
-- url     : https://prove2.me/submissions/a9ba00d7-d3a0-445f-913d-7c46ab3d816f

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open Matrix
open scoped ComplexOrder Kronecker
open ThresholdTheorem

private noncomputable def tvSplit {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) :
    (Q → Fin 2) ≃ ((Fin k → Fin 2) × ({q : Q // q ∉ Set.range s} → Fin 2)) := by
  classical
  apply Equiv.ofBijective (fun x => (x ∘ s, fun q => x q.1))
  constructor
  · intro x y h
    apply funext
    intro q
    by_cases hq : q ∈ Set.range s
    · obtain ⟨i, rfl⟩ := hq
      exact congrFun (congrArg Prod.fst h) i
    · exact congrFun (congrArg Prod.snd h) ⟨q, hq⟩
  · rintro ⟨a, b⟩
    refine ⟨fun q => if hq : q ∈ Set.range s then a (Classical.choose hq)
      else b ⟨q, hq⟩, ?_⟩
    apply Prod.ext
    · apply funext
      intro i
      dsimp
      rw [dif_pos ⟨i, rfl⟩]
      exact congrArg a (s.injective (Classical.choose_spec (show s i ∈ Set.range s from ⟨i, rfl⟩)))
    · ext q
      simp only [dif_neg q.2]

open Classical in
private lemma tv_lift_eq {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s A = (A ⊗ₖ (1 : Matrix ({q : Q // q ∉ Set.range s} → Fin 2) _ ℂ)).submatrix
      (tvSplit s) (tvSplit s) := by
  classical
  ext x y
  change (if ∀ q, q ∉ Set.range s → x q = y q then A (x ∘ s) (y ∘ s) else 0) =
    A (x ∘ s) (y ∘ s) * (1 : Matrix _ _ ℂ) (fun q : {q : Q // q ∉ Set.range s} => x q)
      (fun q : {q : Q // q ∉ Set.range s} => y q)
  simp only [Matrix.one_apply]
  have h : (∀ q, q ∉ Set.range s → x q = y q) ↔
      (fun q : {q : Q // q ∉ Set.range s} => x q) = (fun q : {q : Q // q ∉ Set.range s} => y q) := by
    simp only [funext_iff, Subtype.forall]
  simp only [h]
  split_ifs <;> simp

private lemma tv_lift_mul {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (A B : QMat k) : liftOp s (A * B) = liftOp s A * liftOp s B := by
  classical
  simp only [tv_lift_eq]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]
  simp

private lemma tv_lift_star {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (A : QMat k) :
    liftOp s Aᴴ = (liftOp s A)ᴴ := by
  classical
  simp only [tv_lift_eq, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]

private lemma tv_lift_one {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q) : liftOp s 1 = 1 := by
  classical
  simp only [tv_lift_eq, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

private lemma tv_lift_sum {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (L : List (QMat k)) :
    liftOp s L.sum = (L.map (liftOp s)).sum := by
  classical
  induction L with
  | nil => ext x y; simp [liftOp]
  | cons A L ih =>
    simp only [List.sum_cons, List.map_cons, ← ih]
    ext x y
    simp only [liftOp, Matrix.add_apply]
    split_ifs <;> simp

private lemma tv_complete_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (K : List (QMat k)) (hK : (K.map fun A => Aᴴ * A).sum = 1) :
    (K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum = 1 := by
  classical
  calc
    _ = liftOp s (K.map fun A => Aᴴ * A).sum := by
      simp only [tv_lift_sum, List.map_map, Function.comp_def, tv_lift_mul, tv_lift_star]
    _ = liftOp s 1 := by rw [hK]
    _ = 1 := tv_lift_one s

private lemma tv_apply_pos {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) {ρ : Op Q} (hρ : ρ.PosSemidef) :
    (applyKraus s K ρ).PosSemidef := by
  induction K with
  | nil => exact Matrix.PosSemidef.zero
  | cons A K ih =>
    exact (hρ.mul_mul_conjTranspose_same (liftOp s A)).add ih

private lemma tv_apply_linear {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (ρ σ : Op Q) (a : ℝ) :
    applyKraus s K (ρ - a • σ) = applyKraus s K ρ - a • applyKraus s K σ := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ih]
    module

private lemma tv_apply_trace_aux {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (ρ : Op Q) :
    (applyKraus s K ρ).trace =
      (ρ * (K.map fun A => (liftOp s A)ᴴ * liftOp s A).sum).trace := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, ih]
    congr 1
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]

private lemma tv_apply_trace {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k))
    (hK : (K.map fun A => Aᴴ * A).sum = 1) (ρ : Op Q) :
    (applyKraus s K ρ).trace = ρ.trace := by
  rw [tv_apply_trace_aux, tv_complete_lift s K hK, Matrix.mul_one]

private lemma tv_gate_complete (g : Gate) : g.unitaryᴴ * g.unitary = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hu2 : (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0,0], ![0,1], ![1,0], ![1,1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  have hc2 (x : Fin 2 → Fin 2) : x = ![0,0] ∨ x = ![0,1] ∨ x = ![1,0] ∨ x = ![1,1] := by
    have h := Finset.mem_univ x
    simpa only [hu2, Finset.mem_insert, Finset.mem_singleton] using h
  cases g with
  | H =>
    change hadamardMatᴴ * hadamardMat = 1
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      norm_cast
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [hadamardMat, hu1, Complex.conj_ofReal, ← div_pow,
        div_mul_div_comm, hs, hn] <;>
      field_simp [hn] <;> first | (simpa only [pow_two] using hs.symm) | ring
  | T =>
    change tMatᴴ * tMat = 1
    have he : starRingEnd ℂ (Complex.exp ((Real.pi : ℂ) / 4 * Complex.I)) *
        Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = 1 := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp [map_div, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [tMat, hu1, he]
  | CNOT =>
    change cnotMatᴴ * cnotMat = 1
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc2 x with rfl | rfl | rfl | rfl <;>
      rcases hc2 y with rfl | rfl | rfl | rfl <;>
      simp [cnotMat, hu2]

private lemma tv_ideal_complete (o : Operation) :
    (o.idealKraus.map fun A => Aᴴ * A).sum = 1 := by
  classical
  have hu1 : (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by decide
  have hc1 (x : Fin 1 → Fin 2) : x = ![0] ∨ x = ![1] := by
    have h := Finset.mem_univ x
    simpa only [hu1, Finset.mem_insert, Finset.mem_singleton] using h
  cases o with
  | gate g =>
    change g.unitaryᴴ * g.unitary + 0 = 1
    simpa using tv_gate_complete g
  | wait => simp [Operation.idealKraus]
  | prep =>
    change (resetKraus 0)ᴴ * resetKraus 0 + ((resetKraus 1)ᴴ * resetKraus 1 + 0) = 1
    simp only [add_zero]
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    rcases hc1 x with rfl | rfl <;> rcases hc1 y with rfl | rfl <;>
      simp [resetKraus, hu1, Matrix.mul_apply, Matrix.conjTranspose_apply]


/-! ## Tensoring with the environment -/

private noncomputable def tens {Q : Type*} {m : ℕ} (M : Op Q) (N : Op (Fin m)) :
    Op (Q ⊕ Fin m) :=
  (M ⊗ₖ N).submatrix (Equiv.sumArrowEquivProdArrow Q (Fin m) (Fin 2))
    (Equiv.sumArrowEquivProdArrow Q (Fin m) (Fin 2))

private lemma tens_apply {Q : Type*} {m : ℕ} (M : Op Q) (N : Op (Fin m))
    (a b : Q ⊕ Fin m → Fin 2) :
    tens M N a b = M (fun q => a (Sum.inl q)) (fun q => b (Sum.inl q)) *
      N (fun j => a (Sum.inr j)) (fun j => b (Sum.inr j)) := rfl

private lemma tens_mul {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ} (M1 M2 : Op Q) (N1 N2 : Op (Fin m)) :
    tens M1 N1 * tens M2 N2 = tens (M1 * M2) (N1 * N2) := by
  unfold tens
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

private lemma tens_star {Q : Type*} {m : ℕ} (M : Op Q) (N : Op (Fin m)) :
    (tens M N)ᴴ = tens Mᴴ Nᴴ := by
  unfold tens
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]

private lemma tens_add {Q : Type*} {m : ℕ} (M M' : Op Q) (N : Op (Fin m)) :
    tens (M + M') N = tens M N + tens M' N := by
  ext a b; simp only [tens_apply, Matrix.add_apply, add_mul]

private lemma tens_zero {Q : Type*} {m : ℕ} (N : Op (Fin m)) :
    tens (0 : Op Q) N = 0 := by
  ext a b; simp only [tens_apply, Matrix.zero_apply, zero_mul]

private lemma lift_inl {Q : Type*} [Fintype Q] [DecidableEq Q] {m k : ℕ} (s : Fin k ↪ Q)
    (A : QMat k) :
    liftOp (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin m)) A = tens (liftOp s A) 1 := by
  classical
  ext a b
  rw [tens_apply]
  have hc : (∀ q, q ∉ Set.range (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin m)) →
      a q = b q) ↔ (∀ q, q ∉ Set.range s → a (Sum.inl q) = b (Sum.inl q)) ∧
      (fun j => a (Sum.inr j)) = (fun j => b (Sum.inr j)) := by
    constructor
    · intro h
      refine ⟨fun q hq => h _ ?_, funext fun j => h _ ?_⟩
      · rintro ⟨i, hi⟩
        exact hq ⟨i, Sum.inl_injective hi⟩
      · rintro ⟨i, hi⟩
        simp at hi
    · rintro ⟨h1, h2⟩ (q | j) hq
      · exact h1 q (fun ⟨i, hi⟩ => hq ⟨i, by simp [hi]⟩)
      · exact congrFun h2 j
  have e1 : (fun q => a (Sum.inl q)) ∘ s = a ∘ (s.trans Function.Embedding.inl) := rfl
  have e2 : (fun q => b (Sum.inl q)) ∘ s = b ∘ (s.trans Function.Embedding.inl) := rfl
  unfold liftOp
  rw [e1, e2, Matrix.one_apply]
  by_cases h1 : ∀ q, q ∉ Set.range s → a (Sum.inl q) = b (Sum.inl q)
  · by_cases h2 : (fun j => a (Sum.inr j)) = (fun j => b (Sum.inr j))
    · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
    · rw [if_neg (fun h => h2 (hc.1 h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (hc.1 h).1), if_neg h1, zero_mul]

private lemma apply_tens {Q : Type*} [Fintype Q] [DecidableEq Q] {m k : ℕ} (s : Fin k ↪ Q)
    (K : List (QMat k)) (ρ : Op Q) (E : Op (Fin m)) :
    applyKraus (s.trans (Function.Embedding.inl : Q ↪ Q ⊕ Fin m)) K (tens ρ E) =
      tens (applyKraus s K ρ) E := by
  induction K with
  | nil => simp [applyKraus, tens_zero]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, tens_add, lift_inl, tens_star, tens_mul, tens_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]

private lemma init_tens {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ} :
    initState (Q ⊕ Fin m) = tens (initState Q) (initState (Fin m)) := by
  classical
  ext a b
  rw [tens_apply]
  have h : ∀ c : Q ⊕ Fin m → Fin 2,
      c = 0 ↔ (fun q => c (Sum.inl q)) = 0 ∧ (fun j => c (Sum.inr j)) = 0 := by
    intro c
    simp only [funext_iff, Pi.zero_apply, Sum.forall]
  unfold initState
  rw [h a, h b]
  by_cases h1 : (fun q => a (Sum.inl q)) = 0 <;> by_cases h2 : (fun j => a (Sum.inr j)) = 0 <;>
    by_cases h3 : (fun q => b (Sum.inl q)) = 0 <;> by_cases h4 : (fun j => b (Sum.inr j)) = 0 <;>
    simp [h1, h2, h3, h4]

private lemma dataOut_tens {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ} (ρ : Op Q)
    (x : Q → Fin 2) :
    dataOutDist (tens ρ (initState (Fin m))) x = outDist ρ x := by
  classical
  unfold dataOutDist outDist
  simp only [tens_apply, Sum.elim_inl, Sum.elim_inr]
  have : ∀ y : Fin m → Fin 2, (ρ (fun q => x q) (fun q => x q) * initState (Fin m)
      (fun j => y j) (fun j => y j)).re = if y = 0 then (ρ x x).re else 0 := by
    intro y
    unfold initState
    by_cases hy : y = 0
    · subst hy; simp [Pi.zero_def]
    · simp [hy]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Positivity and normalisation of faulty runs -/

private def Dens {Q : Type*} [Fintype Q] [DecidableEq Q] (ρ : Op Q) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

private lemma dens_apply {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (K : List (QMat k)) (hK : (K.map fun A => Aᴴ * A).sum = 1) {ρ : Op Q} (h : Dens ρ) :
    Dens (applyKraus s K ρ) :=
  ⟨tv_apply_pos s K h.1, by rw [tv_apply_trace s K hK, h.2]⟩

private lemma fold_inv {S α : Type*} (P : S → Prop) (f : S → α → S)
    (hf : ∀ σ a, P σ → P (f σ a)) (L : List α) (σ : S) (h : P σ) : P (L.foldl f σ) := by
  induction L generalizing σ with
  | nil => exact h
  | cons a L ih => exact ih _ (hf σ a h)

private lemma dens_init {Q : Type*} [Fintype Q] [DecidableEq Q] : Dens (initState Q) := by
  classical
  have hd : initState Q = Matrix.diagonal (fun x : Q → Fin 2 => if x = 0 then (1 : ℂ) else 0) := by
    ext x y
    by_cases h : x = y
    · subst y; simp [initState, Matrix.diagonal]
    · simp [initState, Matrix.diagonal, h]
      intro hx hy
      apply h
      rw [hx, hy]
  have hpos : (initState Q).PosSemidef := by
    rw [hd]
    apply Matrix.PosSemidef.diagonal
    intro x
    change 0 ≤ if x = 0 then (1 : ℂ) else 0
    split_ifs <;> simp
  exact ⟨hpos, by simp [initState, Matrix.trace]⟩

private lemma dens_faulty {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (C : Circuit Q) :
    Dens (faultyState F fault C) := by
  unfold faultyState
  refine fold_inv Dens _ ?_ _ _ dens_init
  intro σ Lt hσ
  unfold faultyLayer
  refine fold_inv Dens _ ?_ _ _ hσ
  intro τ ℓj hτ
  split_ifs
  · exact dens_apply _ _ (fault Lt.2 ℓj.2 ℓj.1.op.arity).trace_preserving hτ
  · exact dens_apply _ _ (tv_ideal_complete ℓj.1.op) hτ

private lemma dataOut_nonneg {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (ρ : Op (Q ⊕ Fin m)) (h : Dens ρ) (x : Q → Fin 2) : 0 ≤ dataOutDist ρ x :=
  Finset.sum_nonneg fun y _ => (Complex.nonneg_iff.1 (h.1.diag_nonneg (i := Sum.elim x y))).1

private lemma dataOut_sum {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (ρ : Op (Q ⊕ Fin m)) (h : Dens ρ) : ∑ x, dataOutDist ρ x = 1 := by
  unfold dataOutDist
  rw [← Fintype.sum_prod_type' (f := fun x y => (ρ (Sum.elim x y) (Sum.elim x y)).re)]
  have := Equiv.sum_comp (Equiv.sumArrowEquivProdArrow Q (Fin m) (Fin 2)).symm
    (fun z => (ρ z z).re)
  simp only [Equiv.sumArrowEquivProdArrow] at this
  rw [Equiv.coe_fn_symm_mk] at this
  rw [this, ← Complex.re_sum]
  change ρ.trace.re = 1
  rw [h.2]; rfl

/-! ## Fault-free runs are ideal -/

private lemma faultyLayer_ideal {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (t : ℕ) (L : Layer Q)
    (hF : ∀ ℓj ∈ L.locs.zipIdx, (t, ℓj.2) ∉ F) (ρ : Op Q) :
    faultyLayer F fault t L (tens ρ (initState (Fin m))) =
      tens (idealLayer L ρ) (initState (Fin m)) := by
  have hzip : L.locs.zipIdx.foldl (fun x (a : Location Q × ℕ) =>
      applyKraus a.1.support a.1.op.idealKraus x) ρ = idealLayer L ρ := by
    rw [← List.foldl_map (f := Prod.fst)
      (g := fun x (a : Location Q) => applyKraus a.support a.op.idealKraus x)]
    simp only [List.zipIdx_map_fst, idealLayer]
  rw [← hzip]
  clear hzip
  unfold faultyLayer
  generalize L.locs.zipIdx = E at hF ⊢
  induction E generalizing ρ with
  | nil => rfl
  | cons a E ih =>
    simp only [List.foldl_cons]
    rw [if_neg (hF a List.mem_cons_self), apply_tens]
    exact ih _ (fun b hb => hF b (List.mem_cons_of_mem _ hb))

private def locSet {Q : Type*} [DecidableEq Q] (C : Circuit Q) : Finset (ℕ × ℕ) :=
  (C.zipIdx.flatMap (fun Lt => Lt.1.locs.zipIdx.map (fun ℓj => (Lt.2, ℓj.2)))).toFinset

private lemma mem_locSet {Q : Type*} [DecidableEq Q] (C : Circuit Q) (Lt : Layer Q × ℕ)
    (hLt : Lt ∈ C.zipIdx) (ℓj : Location Q × ℕ) (hℓj : ℓj ∈ Lt.1.locs.zipIdx) :
    (Lt.2, ℓj.2) ∈ locSet C := by
  unfold locSet
  rw [List.mem_toFinset, List.mem_flatMap]
  exact ⟨Lt, hLt, List.mem_map.2 ⟨ℓj, hℓj, rfl⟩⟩

private lemma card_locSet {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    (locSet C).card ≤ C.size := by
  unfold locSet
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  rw [List.length_flatMap, Circuit.size]
  simp only [List.length_map, List.length_zipIdx]
  rw [show (fun Lt : Layer Q × ℕ => Lt.1.locs.length) = (fun L : Layer Q => L.locs.length) ∘ Prod.fst
    from rfl, ← List.map_map, List.zipIdx_map_fst]

private lemma faulty_ideal {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (C : Circuit Q)
    (hF : ∀ a ∈ locSet C, a ∉ F) :
    faultyState F fault C = tens (idealState C) (initState (Fin m)) := by
  have hzip : C.zipIdx.foldl (fun x (a : Layer Q × ℕ) => idealLayer a.1 x) (initState Q) =
      idealState C := by
    rw [← List.foldl_map (f := Prod.fst) (g := fun x (a : Layer Q) => idealLayer a x)]
    simp only [List.zipIdx_map_fst, idealState]
  rw [← hzip]
  clear hzip
  unfold faultyState
  rw [init_tens]
  have hF' : ∀ Lt ∈ C.zipIdx, ∀ ℓj ∈ Lt.1.locs.zipIdx, (Lt.2, ℓj.2) ∉ F :=
    fun Lt hLt ℓj hℓj => hF _ (mem_locSet C Lt hLt ℓj hℓj)
  generalize initState Q = ρ
  generalize C.zipIdx = E at hF' ⊢
  induction E generalizing ρ with
  | nil => rfl
  | cons a E ih =>
    simp only [List.foldl_cons]
    rw [faultyLayer_ideal F fault a.2 a.1 (hF' a List.mem_cons_self)]
    exact ih _ (fun b hb => hF' b (List.mem_cons_of_mem _ hb))

/-! ## Total variation estimates -/

private lemma tv_le_one {α : Type*} [Fintype α] (f g : α → ℝ)
    (hf : ∀ y, 0 ≤ f y) (hg : ∀ y, 0 ≤ g y) (hsf : ∑ y, f y = 1) (hsg : ∑ y, g y = 1) :
    tvDist f g ≤ 1 := by
  unfold tvDist
  have : ∑ y, |f y - g y| ≤ ∑ y, (f y + g y) :=
    Finset.sum_le_sum fun y _ => abs_le.2 ⟨by linarith [hf y, hg y], by linarith [hf y, hg y]⟩
  rw [Finset.sum_add_distrib, hsf, hsg] at this
  linarith

private lemma tv_mixture {α : Type*} [Fintype α] {r : ℕ} (w : Fin r → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (D : Fin r → α → ℝ) (I : α → ℝ) :
    tvDist (fun x => ∑ i, w i * D i x) I ≤ ∑ i, w i * tvDist (D i) I := by
  unfold tvDist
  have key : ∀ x, |(∑ i, w i * D i x) - I x| ≤ ∑ i, w i * |D i x - I x| := by
    intro x
    have : (∑ i, w i * D i x) - I x = ∑ i, w i * (D i x - I x) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_nonneg (hw0 i)]
  calc (1 / 2 : ℝ) * ∑ x, |(∑ i, w i * D i x) - I x|
      ≤ (1 / 2 : ℝ) * ∑ x, ∑ i, w i * |D i x - I x| := by
        gcongr with x; exact key x
    _ = ∑ i, w i * ((1 / 2 : ℝ) * ∑ x, |D i x - I x|) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

theorem solution {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q)
    (e : ℝ) (he : 0 ≤ e) (P : (Q → Fin 2) → ℝ) (hP : IsLocalStochasticDist C e P) :
    tvDist P (outDist (idealState C)) ≤ e * C.size := by
  classical
  obtain ⟨r, m, w, F, fault, hw0, hw1, hS, rfl⟩ := hP
  set I := outDist (idealState C) with hIdef
  set D : Fin r → (Q → Fin 2) → ℝ := fun i => dataOutDist (faultyState (F i) (fault i) C)
    with hDdef
  -- the ideal distribution, realised as a fault-free run
  let triv : ℕ → ℕ → (k : ℕ) → Channel (k + m) := fun _ _ _ => ⟨[1], by simp⟩
  have hI : I = dataOutDist (faultyState ∅ triv C) := by
    rw [faulty_ideal ∅ triv C (fun a _ => Finset.notMem_empty a)]
    funext x; rw [dataOut_tens]
  have hI0 : ∀ x, 0 ≤ I x := by rw [hI]; exact dataOut_nonneg _ (dens_faulty _ _ _)
  have hI1 : ∑ x, I x = 1 := by rw [hI]; exact dataOut_sum _ (dens_faulty _ _ _)
  have htv : ∀ i, tvDist (D i) I ≤ (((locSet C).filter (fun a => a ∈ F i)).card : ℝ) := by
    intro i
    by_cases hb : ((locSet C).filter (fun a => a ∈ F i)).card = 0
    · have hgood : ∀ a ∈ locSet C, a ∉ F i := by
        intro a ha haF
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hb
        exact hb ha haF
      have hDI : D i = I := by
        simp only [hDdef, hIdef]
        rw [faulty_ideal _ _ C hgood]
        funext x; rw [dataOut_tens]
      rw [hDI, hb]
      simp [tvDist]
    · have h1 : (1 : ℝ) ≤ (((locSet C).filter (fun a => a ∈ F i)).card : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
      refine le_trans ?_ h1
      exact tv_le_one _ _ (dataOut_nonneg _ (dens_faulty _ _ _)) hI0
        (dataOut_sum _ (dens_faulty _ _ _)) hI1
  have hunion : ∑ i, w i * (((locSet C).filter (fun a => a ∈ F i)).card : ℝ) ≤
      e * (locSet C).card := by
    have : ∀ i, w i * (((locSet C).filter (fun a => a ∈ F i)).card : ℝ) =
        ∑ a ∈ locSet C, if a ∈ F i then w i else 0 := by
      intro i
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_comm]
    calc ∑ a ∈ locSet C, ∑ i, (if a ∈ F i then w i else 0)
        ≤ ∑ a ∈ locSet C, e := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h := hS {a}
          rw [Finset.card_singleton, pow_one] at h
          rw [← Finset.sum_filter]
          simpa only [Finset.singleton_subset_iff] using h
      _ = e * (locSet C).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc tvDist (fun x => ∑ i, w i * dataOutDist (faultyState (F i) (fault i) C) x) I
      ≤ ∑ i, w i * tvDist (D i) I := tv_mixture w hw0 hw1 D I
    _ ≤ ∑ i, w i * (((locSet C).filter (fun a => a ∈ F i)).card : ℝ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (htv i) (hw0 i)
    _ ≤ e * (locSet C).card := hunion
    _ ≤ e * C.size := by
        gcongr
        exact_mod_cast card_locSet C

