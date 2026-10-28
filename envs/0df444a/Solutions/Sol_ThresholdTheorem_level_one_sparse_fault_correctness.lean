-- Prove2me | solution 1 for ThresholdTheorem.level_one_sparse_fault_correctness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:54:47.057461+00:00
-- url     : https://prove2.me/submissions/0d920129-2a36-48fc-821a-76ff996007e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic
import Theorems.Thm_ThresholdTheorem_level_one_fault_set_reduction

open Matrix
open ThresholdTheorem

/-- One noisy location, with fault probabilities `q` and fault channels `F`. -/
private noncomputable def mpStep {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (σ : Op Q)
    (e : Location Q × (ℕ × ℕ)) : Op Q :=
  (1 - q e.2.1 e.2.2) • applyKraus e.1.support e.1.op.idealKraus σ +
    q e.2.1 e.2.2 • applyKraus e.1.support (F e.2.1 e.2.2 e.1.op.arity).kraus σ

/-- The flat list of all locations of a circuit with their coordinates `(t, j)`. -/
private def mpLocs {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    List (Location Q × (ℕ × ℕ)) :=
  C.zipIdx.flatMap (fun Lt => Lt.1.locs.zipIdx.map (fun ℓj => (ℓj.1, (Lt.2, ℓj.2))))

private lemma mp_noisyState_eq {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ}
    (N : NoiseModel p) (C : Circuit Q) :
    noisyState N C = (mpLocs C).foldl (mpStep N.fault N.prob) (initState Q) := by
  unfold noisyState mpLocs
  rw [List.foldl_flatMap]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  rfl

private lemma mp_locs_nodup {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    ((mpLocs C).map Prod.snd).Nodup := by
  unfold mpLocs
  rw [List.map_flatMap]
  rw [List.nodup_flatMap]
  constructor
  · intro Lt _
    rw [List.map_map]
    have : (Lt.1.locs.zipIdx.map (Prod.snd ∘ fun ℓj : Location Q × ℕ => (ℓj.1, (Lt.2, ℓj.2)))) =
        (Lt.1.locs.zipIdx.map Prod.snd).map (fun j => (Lt.2, j)) := by
      rw [List.map_map]; rfl
    rw [this, List.zipIdx_map_snd]
    exact (List.nodup_range' ).map (fun a b h => (Prod.mk.inj h).2)
  · have h1 : (C.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]; exact List.nodup_range'
    rw [List.Nodup, List.pairwise_map] at h1
    refine h1.imp fun {a b} hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro x hxa hxb
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hxa hxb
    obtain ⟨u, -, rfl⟩ := hxa
    obtain ⟨v, -, hv⟩ := hxb
    exact hab (Prod.mk.inj hv).1.symm

private lemma mp_applyKraus_comb {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (s : Fin k ↪ Q) (K : List (QMat k)) (a b : ℝ) (X Y : Op Q) :
    applyKraus s K (a • X + b • Y) = a • applyKraus s K X + b • applyKraus s K Y := by
  induction K with
  | nil => simp [applyKraus]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
    module

private lemma mp_fold_comb {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ)
    (E : List (Location Q × (ℕ × ℕ))) (a b : ℝ) (X Y : Op Q) :
    E.foldl (mpStep F q) (a • X + b • Y) =
      a • E.foldl (mpStep F q) X + b • E.foldl (mpStep F q) Y := by
  induction E generalizing X Y with
  | nil => rfl
  | cons e E ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [mpStep, mp_applyKraus_comb]
    module

/-- Update of the fault probability at one location. -/
private def mpUpd (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ) (v : ℝ) : ℕ → ℕ → ℝ :=
  fun t j => if (t, j) = a then v else q t j

private lemma mp_fold_congr {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q q' : ℕ → ℕ → ℝ)
    (E : List (Location Q × (ℕ × ℕ)))
    (h : ∀ e ∈ E, q e.2.1 e.2.2 = q' e.2.1 e.2.2) (σ : Op Q) :
    E.foldl (mpStep F q) σ = E.foldl (mpStep F q') σ :=
  List.foldl_ext _ _ _ fun σ e he => by simp only [mpStep, h e he]

private lemma mp_fold_split {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (a : ℕ × ℕ)
    (E : List (Location Q × (ℕ × ℕ))) (hE : (E.map Prod.snd).Nodup) (σ : Op Q) :
    E.foldl (mpStep F q) σ =
      (1 - q a.1 a.2) • E.foldl (mpStep F (mpUpd q a 0)) σ +
        q a.1 a.2 • E.foldl (mpStep F (mpUpd q a 1)) σ := by
  induction E generalizing σ with
  | nil => simp only [List.foldl_nil]; module
  | cons e E ih =>
    simp only [List.map_cons, List.nodup_cons] at hE
    obtain ⟨hnot, hE⟩ := hE
    simp only [List.foldl_cons]
    by_cases he : e.2 = a
    · have hc : ∀ v, ∀ e' ∈ E, mpUpd q a v e'.2.1 e'.2.2 = q e'.2.1 e'.2.2 := by
        intro v e' he'
        have : e'.2 ≠ a := by
          rintro h; apply hnot; rw [he, ← h]; exact List.mem_map_of_mem he'
        simp only [mpUpd, Prod.mk.eta, if_neg this]
      rw [mp_fold_congr F (mpUpd q a 0) q E (hc 0), mp_fold_congr F (mpUpd q a 1) q E (hc 1),
        ← mp_fold_comb]
      congr 1
      have h0 : mpUpd q a 0 e.2.1 e.2.2 = 0 := by simp [mpUpd, Prod.mk.eta, he]
      have h1 : mpUpd q a 1 e.2.1 e.2.2 = 1 := by simp [mpUpd, Prod.mk.eta, he]
      have hq : q e.2.1 e.2.2 = q a.1 a.2 := by rw [← he]
      simp only [mpStep, h0, h1, hq]
      module
    · have hs : ∀ v, mpStep F (mpUpd q a v) σ e = mpStep F q σ e := by
        intro v
        simp only [mpStep, mpUpd, Prod.mk.eta, if_neg he]
      rw [hs 0, hs 1]
      exact ih hE _


/-! ## Transport from `Q` to `Q ⊕ Fin 0` -/

private noncomputable def nmE (Q : Type*) : (Q ⊕ Fin 0 → Fin 2) ≃ (Q → Fin 2) :=
  Equiv.arrowCongr (Equiv.sumEmpty Q (Fin 0)) (Equiv.refl (Fin 2))

private lemma nmE_apply {Q : Type*} (x : Q ⊕ Fin 0 → Fin 2) : nmE Q x = fun q => x (Sum.inl q) := by
  funext q; simp [nmE]

private noncomputable def nmPhi {Q : Type*} (ρ : Op Q) : Op (Q ⊕ Fin 0) :=
  ρ.submatrix (nmE Q) (nmE Q)

private lemma nmPhi_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (s' : Fin k ↪ Q ⊕ Fin 0) (hs : ∀ i, s' i = Sum.inl (s i)) (A : QMat k) :
    nmPhi (liftOp s A) = liftOp s' A := by
  classical
  ext x y
  simp only [nmPhi, submatrix_apply, liftOp, nmE_apply]
  have h1 : (fun i => x (s' i)) = (fun i => x (Sum.inl (s i))) := funext fun i => by rw [hs]
  have h2 : (fun i => y (s' i)) = (fun i => y (Sum.inl (s i))) := funext fun i => by rw [hs]
  have hc : (∀ q, q ∉ Set.range s → x (Sum.inl q) = y (Sum.inl q)) ↔
      (∀ z, z ∉ Set.range s' → x z = y z) := by
    constructor
    · intro h z hz
      rcases z with q | e
      · apply h q
        rintro ⟨i, rfl⟩
        exact hz ⟨i, hs i⟩
      · exact e.elim0
    · intro h q hq
      apply h
      rintro ⟨i, hi⟩
      rw [hs] at hi
      exact hq ⟨i, Sum.inl_injective hi⟩
  simp only [Function.comp_def, hc, h1, h2]

private lemma nmPhi_apply {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (s : Fin k ↪ Q)
    (s' : Fin k ↪ Q ⊕ Fin 0) (hs : ∀ i, s' i = Sum.inl (s i)) (K : List (QMat k)) (ρ : Op Q) :
    nmPhi (applyKraus s K ρ) = applyKraus s' K (nmPhi ρ) := by
  induction K with
  | nil => simp [applyKraus, nmPhi]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [← ih, ← nmPhi_lift s s' hs]
    simp only [nmPhi, submatrix_mul_equiv, conjTranspose_submatrix]
    rfl

private lemma nmPhi_init {Q : Type*} : nmPhi (initState Q) = initState (Q ⊕ Fin 0) := by
  classical
  ext x y
  simp only [nmPhi, submatrix_apply, initState, nmE_apply]
  have hz : ∀ z : Q ⊕ Fin 0 → Fin 2, ((fun q => z (Sum.inl q)) = 0) ↔ z = 0 := by
    intro z
    constructor
    · intro h; funext w
      rcases w with q | e
      · exact congrFun h q
      · exact e.elim0
    · rintro rfl; rfl
  simp only [hz]

private lemma nmPhi_data {Q : Type*} (ρ : Op Q) (x : Q → Fin 2) :
    dataOutDist (nmPhi ρ) x = outDist ρ x := by
  simp only [dataOutDist, nmPhi, submatrix_apply, nmE_apply, Fintype.sum_unique, outDist]
  rfl

private lemma nm_envEmbed {Q : Type*} {k : ℕ} (s : Fin k ↪ Q) (i : Fin (k + 0)) :
    envEmbed 0 s i = Sum.inl (s i) := by
  simp [envEmbed, Fin.addCases]
  rfl

/-! ## Faulty executions as a flat fold -/

private noncomputable def nmFStep {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + 0)) (σ : Op (Q ⊕ Fin 0))
    (e : Location Q × (ℕ × ℕ)) : Op (Q ⊕ Fin 0) :=
  if (e.2.1, e.2.2) ∈ F then
    applyKraus (envEmbed 0 e.1.support) (fault e.2.1 e.2.2 e.1.op.arity).kraus σ
  else
    applyKraus (e.1.support.trans Function.Embedding.inl) e.1.op.idealKraus σ

private lemma nm_faultyState_eq {Q : Type*} [Fintype Q] [DecidableEq Q]
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + 0)) (C : Circuit Q) :
    faultyState F fault C = (mpLocs C).foldl (nmFStep F fault) (initState (Q ⊕ Fin 0)) := by
  unfold faultyState mpLocs
  rw [List.foldl_flatMap]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  rfl

private lemma nm_fold_rel {Q : Type*} [Fintype Q] [DecidableEq Q]
    (fault : ℕ → ℕ → (k : ℕ) → Channel k) (q : ℕ → ℕ → ℝ) (F : Finset (ℕ × ℕ))
    (E : List (Location Q × (ℕ × ℕ)))
    (hE : ∀ e ∈ E, (q e.2.1 e.2.2 = 1 ∧ (e.2.1, e.2.2) ∈ F) ∨
      (q e.2.1 e.2.2 = 0 ∧ (e.2.1, e.2.2) ∉ F)) (σ : Op Q) :
    nmPhi (E.foldl (mpStep fault q) σ) = E.foldl (nmFStep F fault) (nmPhi σ) := by
  induction E generalizing σ with
  | nil => rfl
  | cons e E ih =>
    simp only [List.foldl_cons]
    rw [ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))]
    congr 1
    rcases hE e List.mem_cons_self with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [mpStep, nmFStep, h1, if_pos h2, sub_self, zero_smul, one_smul, zero_add]
      exact nmPhi_apply _ _ (nm_envEmbed _) _ _
    · simp only [mpStep, nmFStep, h1, if_neg h2, sub_zero, zero_smul, one_smul, add_zero]
      exact nmPhi_apply _ _ (fun i => rfl) _ _

/-! ## Bridge: deterministic `NoiseModel 1` runs are faulty runs with `m = 0` -/

private lemma sp_bridge {Q : Type*} [Fintype Q] [DecidableEq Q] {p : ℝ} (N : NoiseModel p)
    (C : Circuit Q) (h01 : ∀ t j, N.prob t j = 0 ∨ N.prob t j = 1) :
    outDist (noisyState N C) = dataOutDist (faultyState (m := 0)
      (((mpLocs C).map Prod.snd).toFinset.filter (fun l => N.prob l.1 l.2 = 1)) N.fault C) := by
  classical
  funext x
  rw [mp_noisyState_eq, nm_faultyState_eq, ← nmPhi_init, ← nm_fold_rel N.fault N.prob, nmPhi_data]
  intro e he
  have hm : (e.2.1, e.2.2) ∈ ((mpLocs C).map Prod.snd).toFinset := by
    simp only [Prod.mk.eta, List.mem_toFinset]
    exact List.mem_map_of_mem he
  rcases h01 e.2.1 e.2.2 with h | h
  · right
    refine ⟨h, fun hF => ?_⟩
    have := (Finset.mem_filter.1 hF).2
    rw [h] at this
    norm_num at this
  · left
    exact ⟨h, Finset.mem_filter.2 ⟨hm, h⟩⟩

/-! ## Ideal runs with an idle environment -/

open Kronecker

private def spE (Q : Type*) (m : ℕ) : (Q ⊕ Fin m → Fin 2) ≃ (Q → Fin 2) × (Fin m → Fin 2) :=
  Equiv.sumArrowEquivProdArrow Q (Fin m) (Fin 2)

private noncomputable def spT {Q : Type*} (m : ℕ) (ρ : Op Q) : Op (Q ⊕ Fin m) :=
  (ρ ⊗ₖ initState (Fin m)).submatrix (spE Q m) (spE Q m)

private lemma spT_add {Q : Type*} (m : ℕ) (X Y : Op Q) : spT m (X + Y) = spT m X + spT m Y := by
  ext x y; simp [spT, Matrix.add_kronecker]

private lemma spT_zero {Q : Type*} (m : ℕ) : spT m (0 : Op Q) = 0 := by
  ext x y; simp [spT]

private lemma sp_lift {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (m : ℕ) (s : Fin k ↪ Q)
    (A : QMat k) :
    liftOp (s.trans (Function.Embedding.inl (β := Fin m))) A =
      (liftOp s A ⊗ₖ (1 : Op (Fin m))).submatrix (spE Q m) (spE Q m) := by
  classical
  ext x y
  have hx1 : (spE Q m x).1 = fun q => x (Sum.inl q) := rfl
  have hy1 : (spE Q m y).1 = fun q => y (Sum.inl q) := rfl
  have hx2 : (spE Q m x).2 = fun j => x (Sum.inr j) := rfl
  have hy2 : (spE Q m y).2 = fun j => y (Sum.inr j) := rfl
  simp only [liftOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    hx1, hy1, hx2, hy2]
  have hc : (∀ z, z ∉ Set.range (s.trans (Function.Embedding.inl (β := Fin m))) → x z = y z) ↔
      ((∀ q, q ∉ Set.range s → x (Sum.inl q) = y (Sum.inl q)) ∧
        (fun j => x (Sum.inr j)) = (fun j => y (Sum.inr j))) := by
    constructor
    · intro h
      refine ⟨fun q hq => h _ ?_, funext fun j => h _ ?_⟩
      · rintro ⟨i, hi⟩
        simp only [Function.Embedding.trans_apply, Function.Embedding.inl_apply] at hi
        exact hq ⟨i, Sum.inl_injective hi⟩
      · rintro ⟨i, hi⟩
        simp at hi
    · rintro ⟨h1, h2⟩ z hz
      rcases z with q | j
      · apply h1 q
        rintro ⟨i, rfl⟩
        exact hz ⟨i, rfl⟩
      · exact congrFun h2 j
  by_cases h1 : ∀ q, q ∉ Set.range s → x (Sum.inl q) = y (Sum.inl q)
  · by_cases h2 : (fun j => x (Sum.inr j)) = (fun j => y (Sum.inr j))
    · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
      rfl
    · rw [if_neg (fun H => h2 (hc.1 H).2), if_neg h2, mul_zero]
  · rw [if_neg (fun H => h1 (hc.1 H).1), if_neg h1, zero_mul]

private lemma spT_apply {Q : Type*} [Fintype Q] [DecidableEq Q] {k : ℕ} (m : ℕ) (s : Fin k ↪ Q)
    (K : List (QMat k)) (ρ : Op Q) :
    applyKraus (s.trans Function.Embedding.inl) K (spT m ρ) = spT m (applyKraus s K ρ) := by
  induction K with
  | nil => simp [applyKraus, spT_zero]
  | cons A K ih =>
    simp only [applyKraus, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, spT_add, sp_lift]
    congr 1
    simp only [spT, Matrix.submatrix_mul_equiv, Matrix.conjTranspose_submatrix,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]

private lemma spT_init {Q : Type*} (m : ℕ) : spT m (initState Q) = initState (Q ⊕ Fin m) := by
  classical
  ext x y
  have hx1 : (spE Q m x).1 = x ∘ Sum.inl := rfl
  have hy1 : (spE Q m y).1 = y ∘ Sum.inl := rfl
  have hx2 : (spE Q m x).2 = x ∘ Sum.inr := rfl
  have hy2 : (spE Q m y).2 = y ∘ Sum.inr := rfl
  simp only [spT, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, initState, hx1, hx2, hy1, hy2]
  have hz : ∀ z : Q ⊕ Fin m → Fin 2, z = 0 ↔ (z ∘ Sum.inl = 0 ∧ z ∘ Sum.inr = 0) := by
    intro z
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩; funext w
      rcases w with q | j
      · exact congrFun h1 q
      · exact congrFun h2 j
  rw [hz x, hz y]
  by_cases a1 : x ∘ Sum.inl = 0 <;> by_cases a2 : x ∘ Sum.inr = 0 <;>
    by_cases a3 : y ∘ Sum.inl = 0 <;> by_cases a4 : y ∘ Sum.inr = 0 <;> simp [a1, a2, a3, a4]

private lemma spT_data {Q : Type*} (m : ℕ) (ρ : Op Q) (x : Q → Fin 2) :
    dataOutDist (spT m ρ) x = outDist ρ x := by
  classical
  have he : ∀ y : Fin m → Fin 2, spE Q m (Sum.elim x y) = (x, y) := fun y => rfl
  simp only [dataOutDist, spT, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, he,
    initState, and_self, outDist]
  rw [Finset.sum_eq_single (0 : Fin m → Fin 2)]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Faulty runs with general `m` as a flat fold -/

private noncomputable def spFStep {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (σ : Op (Q ⊕ Fin m))
    (e : Location Q × (ℕ × ℕ)) : Op (Q ⊕ Fin m) :=
  if (e.2.1, e.2.2) ∈ F then
    applyKraus (envEmbed m e.1.support) (fault e.2.1 e.2.2 e.1.op.arity).kraus σ
  else
    applyKraus (e.1.support.trans Function.Embedding.inl) e.1.op.idealKraus σ

private lemma sp_faultyState_eq {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (C : Circuit Q) :
    faultyState F fault C = (mpLocs C).foldl (spFStep F fault) (initState (Q ⊕ Fin m)) := by
  unfold faultyState mpLocs
  rw [List.foldl_flatMap]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  rfl

private lemma sp_foldl_zipIdx {α β : Type*} (l : List α) (n : ℕ) (f : β → α → β) (a : β) :
    (l.zipIdx n).foldl (fun σ p => f σ p.1) a = l.foldl f a := by
  conv_rhs => rw [← List.zipIdx_map_fst n l]
  rw [List.foldl_map]

private lemma sp_idealState_eq {Q : Type*} [Fintype Q] [DecidableEq Q] (C : Circuit Q) :
    idealState C = (mpLocs C).foldl
      (fun σ e => applyKraus e.1.support e.1.op.idealKraus σ) (initState Q) := by
  unfold idealState mpLocs
  rw [List.foldl_flatMap]
  rw [← sp_foldl_zipIdx C 0 (fun σ L => idealLayer L σ)]
  congr 1
  funext σ Lt
  rw [List.foldl_map]
  unfold idealLayer
  rw [← sp_foldl_zipIdx Lt.1.locs 0]

private lemma sp_fold_ideal {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m))
    (E : List (Location Q × (ℕ × ℕ))) (hE : ∀ e ∈ E, (e.2.1, e.2.2) ∉ F) (σ : Op Q) :
    E.foldl (spFStep F fault) (spT m σ) =
      spT m (E.foldl (fun σ e => applyKraus e.1.support e.1.op.idealKraus σ) σ) := by
  induction E generalizing σ with
  | nil => rfl
  | cons e E ih =>
    simp only [List.foldl_cons]
    rw [← ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))]
    congr 1
    simp only [spFStep, if_neg (hE e List.mem_cons_self)]
    exact spT_apply m _ _ _

private lemma sp_ideal_of_disjoint {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (F : Finset (ℕ × ℕ)) (fault : ℕ → ℕ → (k : ℕ) → Channel (k + m)) (C : Circuit Q)
    (hF : ∀ l ∈ F, l ∉ (mpLocs C).map Prod.snd) :
    dataOutDist (faultyState F fault C) = outDist (idealState C) := by
  funext x
  rw [sp_faultyState_eq, ← spT_init m, sp_fold_ideal, spT_data, sp_idealState_eq]
  intro e he hmem
  exact hF _ hmem (by simpa using List.mem_map_of_mem (f := Prod.snd) he)

private lemma sp_locs_length {Q : Type*} [DecidableEq Q] (C : Circuit Q) :
    (mpLocs C).length = C.size := by
  unfold mpLocs Circuit.size
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_zipIdx]
  conv_rhs => rw [← List.zipIdx_map_fst 0 C]
  rw [List.map_map]
  rfl

/-! ## The reduction -/

theorem solution :
    ∃ (M A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * C.size ∧
        ∃ B : Finset ((ℕ × ℕ) × (ℕ × ℕ)), (B.card : ℝ) ≤ M * C.size ∧
          (∀ x ∈ B, x.1 ≠ x.2) ∧
          ∀ N : NoiseModel 1, (∀ t j, N.prob t j = 0 ∨ N.prob t j = 1) →
            (∀ x ∈ B, N.prob x.1.1 x.1.2 = 0 ∨ N.prob x.2.1 x.2.2 = 0) →
            decodeDist dec (outDist (noisyState N C')) = outDist (idealState C) := by
  classical
  obtain ⟨M, A, b, dec, hred⟩ := ThresholdTheorem.level_one_fault_set_reduction
  refine ⟨2 * M, A, b, dec, ?_⟩
  intro n C
  obtain ⟨C', hsize, pairs, Φ, hcard, htwo, hwit, hrep⟩ := hred (Fin n) C
  refine ⟨C', hsize, ?_⟩
  let L : Finset (ℕ × ℕ) := ((mpLocs C).map Prod.snd).toFinset
  let B : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := L.biUnion fun l => (pairs l).biUnion fun p => p.offDiag
  refine ⟨B, ?_, ?_, ?_⟩
  · -- cardinality
    have h1 : B.card ≤ 2 * M * L.card := by
      refine (Finset.card_biUnion_le).trans ?_
      have : ∀ l ∈ L, ((pairs l).biUnion fun p => p.offDiag).card ≤ 2 * M := by
        intro l _
        refine (Finset.card_biUnion_le).trans ?_
        have : ∀ p ∈ pairs l, p.offDiag.card = 2 := by
          intro p hp
          rw [Finset.offDiag_card, htwo l p hp]
        rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
        have := hcard l
        omega
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h2 : L.card ≤ C.size := by
      rw [← sp_locs_length]
      exact (List.toFinset_card_le _).trans (by simp)
    have h3 : B.card ≤ 2 * M * C.size := h1.trans (Nat.mul_le_mul_left _ h2)
    exact_mod_cast h3
  · intro x hx
    simp only [B, Finset.mem_biUnion, Finset.mem_offDiag] at hx
    obtain ⟨_, _, _, _, _, _, h⟩ := hx
    exact h
  · intro N h01 hB
    obtain ⟨m', hm'⟩ := hrep 0
    set F := ((mpLocs C').map Prod.snd).toFinset.filter (fun l => N.prob l.1 l.2 = 1) with hFdef
    obtain ⟨fault', hfault'⟩ := hm' F N.fault
    have hdec : decodeDist dec (outDist (noisyState N C')) =
        pushDist (blockMap dec) (outDist (noisyState N C')) := by
      funext y
      simp only [decodeDist, pushDist]
      exact Finset.sum_congr (by ext x; simp only [Finset.mem_filter]; rfl) (fun _ _ => rfl)
    rw [hdec, sp_bridge N C' h01, ← hFdef, hfault']
    apply sp_ideal_of_disjoint
    intro l hl hlC
    obtain ⟨g, hg, -⟩ := hwit F {l} (by simpa using hl)
    obtain ⟨hgp, hgF⟩ := hg l (Finset.mem_singleton_self l)
    obtain ⟨a, c, hac, hgeq⟩ := Finset.card_eq_two.1 (htwo l (g l) hgp)
    have hmem : (a, c) ∈ B := by
      simp only [B, Finset.mem_biUnion, Finset.mem_offDiag]
      exact ⟨l, by simpa [L] using hlC, g l, hgp, by rw [hgeq]; simp, by rw [hgeq]; simp, hac⟩
    have ha : N.prob a.1 a.2 = 1 := (Finset.mem_filter.1 (hgF (by rw [hgeq]; simp))).2
    have hc : N.prob c.1 c.2 = 1 := (Finset.mem_filter.1 (hgF (by rw [hgeq]; simp))).2
    rcases hB _ hmem with h | h
    · rw [ha] at h; norm_num at h
    · rw [hc] at h; norm_num at h

#print axioms solution
