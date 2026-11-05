-- Prove2me | solution 1 for StrongConv.tendsto_mul_uniformExp_trN_wordEval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:40:42.483303+00:00
-- url     : https://prove2.me/submissions/59f12278-e405-436a-b96b-66c977997711

import Definitions.Def_StrongConv
import Mathlib

section
section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

/-! ## Part Root: roots in free groups -/

/-! ## Part Perm: words as permutations -/

/-! ## Part Comb: the expected number of fixed points -/

/-! ## Part Alg: clearing denominators -/

end StrongConv.S5
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

theorem trN_wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    trN N (wordEval (sModel σ) w) = ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trN]
  rw [trN, wordEval_sModel, trace_permOpPerp hN]
  simp

/-! ### The left-regular representation -/

end StrongConv.S5.PartPerm
end
end

section
/-!
# Part Comb: the expected number of fixed points of a random word permutation

Proof of `StrongConv.S5.exists_fixCount_expectation` (stated in `Blueprint.lean`).
-/

open Finset

noncomputable section

namespace StrongConv.S5.PartComb

open StrongConv StrongConv.S5

/-! ## Counting permutations extending a partial injection -/

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext (E : Finset (α × α)) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      if PInj E then (Fintype.card α - E.card).factorial else 0 := by
  split_ifs with h
  · obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
    have hA : (E.image Prod.fst).card = E.card :=
      card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
    rw [← hA, ← card_stab]
    refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
      intro a ha
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
      rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
      simp
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro p hp
      rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
    · intro τ _; simp
    · intro π _; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    apply h
    intro p hp q hq
    constructor
    · intro e; rw [← hτ p hp, ← hτ q hq, e]
    · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end Count

/-! ## Paths along a word -/

section Word

variable {d : ℕ} (w : List (Letter d))

/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

lemma edge_cases {α : Type*} (l : Letter d) (a b : α) :
    ((edge l a b).1 = a ∧ (edge l a b).2 = b) ∨ ((edge l a b).1 = b ∧ (edge l a b).2 = a) := by
  rcases l with _ | i | i <;> simp [edge]

lemma edge_map {α β : Type*} (φ : β → α) (l : Letter d) (a b : β) :
    edge l (φ a) (φ b) = Prod.map φ φ (edge l a b) := by
  rcases l with _ | i | i <;> simp [edge]

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

/-- The path of `y` under `σ`. -/
def path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) : Fin (w.length + 1) → Fin N :=
  fun t => wordPerm σ (w.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Letter d)
    (ws : List (Letter d)) (y : Fin N) :
    wordPerm σ (l :: ws) y = letterPerm σ l (wordPerm σ ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y 0 = wordPerm σ w y := by
  simp [path]

lemma path_step {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) (t : Fin w.length) :
    path w σ y t.castSucc = letterPerm σ (w.get t) (path w σ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N)
    (hx : Rz w σ x) : x = path w σ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    fixCount (wordPerm σ w) =
      (univ.filter fun x : Fin (w.length + 1) → Fin N => Rz w σ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path w σ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path w σ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step w σ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path w σ x hx.1).symm
  · intro y _
    exact path_last w σ y

lemma Rz_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Rz w σ x ↔ Cons w x ∧ ∀ i, ∀ p ∈ Es w x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun t ht => by have := h t; rw [ht] at this; simpa [letterPerm] using this, ?_⟩
    intro i p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [mem_filter] at ht
    have h' := h t
    generalize w.get t = l at ht h'
    rcases l with _ | j | j
    · simp [lab] at ht
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge]; exact h'.symm
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge, letterPerm] at h' ⊢
      rw [h']; simp
  · rintro ⟨hc, he⟩ t
    have hmem : ∀ j, lab (w.get t) = some j →
        edge (w.get t) (x t.castSucc) (x t.succ) ∈ Es w x j := fun j hj =>
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hj⟩, rfl⟩
    have hct := hc t
    generalize w.get t = l at hmem hct
    rcases l with _ | j | j
    · simp [letterPerm, hct rfl]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, this]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, ← this]

lemma card_Rz {N : ℕ} (x : Fin (w.length + 1) → Fin N) :
    (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => Rz w σ x).card =
      if Cons w x then
        ∏ i, (if PInj (Es w x i) then (N - (Es w x i).card).factorial else 0)
      else 0 := by
  split_ifs with hc
  · have : (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => Rz w σ x) =
        Fintype.piFinset (fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
          ∀ p ∈ Es w x i, τ p.1 = p.2) := by
      ext σ; simp [Rz_iff, hc, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_ext, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    exact hc ((Rz_iff w σ x).1 h).1

/-- The weight of a path. -/
def G (N : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : ℕ :=
  if Good w x then ∏ i, (N - (Es w x i).card).factorial else 0

lemma sum_fixCount (N : ℕ) :
    ∑ σ : Fin d → Equiv.Perm (Fin N), fixCount (wordPerm σ w) =
      ∑ x : Fin (w.length + 1) → Fin N, G w N x := by
  simp only [fixCount_eq, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  by_cases hcl : x 0 = x (Fin.last _)
  · simp only [hcl, and_true]
    rw [card_Rz, G]
    by_cases hg : Good w x
    · rw [if_pos hg, if_pos hg.1]
      exact prod_congr rfl fun i _ => if_pos (hg.2.1 i)
    · rw [if_neg hg]
      split_ifs with hc
      · have : ¬ ∀ i, PInj (Es w x i) := fun h => hg ⟨hc, h, hcl⟩
        push Not at this
        obtain ⟨i, hi⟩ := this
        exact prod_eq_zero (mem_univ i) (if_neg hi)
      · rfl
  · simp only [hcl, and_false, G]
    rw [if_neg (fun h => hcl h.2.2)]
    simp

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-- The first position where `x` takes the value `x t`. -/
def canon (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

/-- The number of values of a path. -/
def nv (x : Fin n → α) : ℕ := (univ.image x).card

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [Fintype β] in
lemma Es_comp (c : Fin (w.length + 1) → β) (φ : β → α) (i : Fin d) :
    Es w (φ ∘ c) i = (Es w c i).image (Prod.map φ φ) := by
  simp only [Es, image_image]
  refine image_congr fun t _ => ?_
  simp [edge_map]

omit [Fintype β] in
lemma Es_range (c : Fin (w.length + 1) → β) (i : Fin d) (p : β × β) (hp : p ∈ Es w c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  rcases edge_cases (w.get t) (c t.castSucc) (c t.succ) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

omit [Fintype α] [Fintype β] in
lemma card_Es_comp (i : Fin d) : (Es w (φ ∘ c) i).card = (Es w c i).card := by
  rw [Es_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := Es_range w c i p hp
  have hq' := Es_range w c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

lemma good_comp : Good w (φ ∘ c) ↔ Good w c := by
  have key : ∀ s t, φ (c s) = φ (c t) ↔ c s = c t := fun s t =>
    hφ.eq_iff ⟨s, rfl⟩ ⟨t, rfl⟩
  have hP : ∀ i, PInj (Es w (φ ∘ c) i) ↔ PInj (Es w c i) := by
    intro i
    rw [Es_comp]
    unfold PInj
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
      Prod.map_snd]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    have hp' := Es_range w c i p hp
    have hq' := Es_range w c i q hq
    rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]
  unfold Good Cons
  simp only [Function.comp, key, hP]

lemma G_comp (N : ℕ) : G w N (φ ∘ c) = G w N c := by
  unfold G
  simp only [good_comp w c φ hφ, card_Es_comp w c φ hφ]

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

lemma sum_card_Es_le (x : Fin (w.length + 1) → α) : ∑ i, (Es w x i).card ≤ w.length := by
  calc ∑ i, (Es w x i).card
      ≤ ∑ i, (univ.filter fun t : Fin w.length => lab (w.get t) = some i).card :=
        sum_le_sum fun i _ => card_image_le
    _ = (univ.biUnion fun i => univ.filter fun t : Fin w.length => lab (w.get t) = some i).card := by
        rw [card_biUnion]
        intro i _ j _ hij
        show Disjoint _ _
        rw [disjoint_filter]
        intro t _ hi hj
        exact hij (Option.some.inj (hi.symm.trans hj))
    _ ≤ w.length := (card_le_univ _).trans (Fintype.card_fin _).le

end Bounds

end StrongConv.S5.PartComb
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
/-!
# CGTvH Lemma 5.2 (Nica): Blueprint

`E[fix w(σ)] = ∑_{c} N^{(V c)} / ∏ᵢ N^{(Eᵢ c)}` over the canonical consistent colourings `c` of the
closed path of `w` (S5 PartComb). For `w` replaced by `r^k`, `r` a cyclically reduced word of a
conjugate of the non-power `v`, every colouring has `V ≤ E`, and exactly `d(k)` have `V = E`
(the periodic ones).
-/
/-- The inverse letter. -/
def letterInv {d : ℕ} : Letter d → Letter d
  | none => none
  | some s => some s.swap

/-- `r` is cyclically reduced: no letter is followed (cyclically) by its inverse. -/
def CycRed {d : ℕ} (r : List (Letter d)) : Prop :=
  ∀ t : Fin r.length,
    r.get ⟨(t.val + 1) % r.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ letterInv (r.get t)

/-- `r^k` as a word. -/
def powList {d : ℕ} (r : List (Letter d)) (k : ℕ) : List (Letter d) :=
  (List.replicate k r).flatten

/-- Canonical good colourings of the closed path of `u`. -/
def CG {d : ℕ} (u : List (Letter d)) : Finset (Fin (u.length + 1) → Fin (u.length + 1)) :=
  (univ.filter fun c => canon c = c).filter (Good u)

/-- The number of edges of a colouring. -/
def Ecount {d : ℕ} (u : List (Letter d)) (c : Fin (u.length + 1) → Fin (u.length + 1)) : ℕ :=
  ∑ i, (Es u c i).card

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartW
/-! ## Cyclically reduced representatives -/
/-- A letter of a reduced word of `FreeGroup (Fin d)` as a `Letter d`. -/
def toLetter {d : ℕ} (p : Fin d × Bool) : Letter d :=
  if p.2 then some (Sum.inl p.1) else some (Sum.inr p.1)

lemma toLetter_ne_none {d : ℕ} (p : Fin d × Bool) : toLetter p ≠ none := by
  unfold toLetter; split <;> simp

lemma toLetter_injective {d : ℕ} : Function.Injective (toLetter (d := d)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  cases a <;> cases b <;> simp_all [toLetter]

lemma letterInv_toLetter {d : ℕ} (p : Fin d × Bool) :
    letterInv (toLetter p) = toLetter (p.1, !p.2) := by
  rcases p with ⟨i, a⟩
  cases a <;> rfl

lemma wordFree_cons {d : ℕ} (l : Letter d) (w : List (Letter d)) :
    wordFree (l :: w) = wordFree [l] * wordFree w := by
  simp [wordFree]

lemma wordFree_map_toLetter {d : ℕ} (R : List (Fin d × Bool)) :
    wordFree (R.map toLetter) = FreeGroup.mk R := by
  induction R with
  | nil => simp [wordFree, FreeGroup.one_eq_mk]
  | cons a R ih =>
    rw [List.map_cons, wordFree_cons, ih,
      show a :: R = [a] ++ R from rfl, ← FreeGroup.mul_mk]
    congr 1
    rcases a with ⟨i, b⟩
    cases b
    · simp [wordFree, toLetter, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
    · simp [wordFree, toLetter, FreeGroup.of]

theorem exists_cyc_rep {d : ℕ} (v : FreeGroup (Fin d)) (hv : IsNonPower v) :
    ∃ (r : List (Letter d)) (h : FreeGroup (Fin d)), r ≠ [] ∧ (∀ l ∈ r, l ≠ none) ∧
      CycRed r ∧ wordFree r = h * v * h⁻¹ := by
  classical
  set L := v.toWord
  set R := FreeGroup.reduceCyclically L with hRdef
  set C := FreeGroup.reduceCyclically.conjugator L
  have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  have hv' : v = FreeGroup.mk C * FreeGroup.mk R * (FreeGroup.mk C)⁻¹ := by
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk, hconj, FreeGroup.mk_toWord]
  have hRc : FreeGroup.IsCyclicallyReduced R :=
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  refine ⟨R.map toLetter, (FreeGroup.mk C)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [List.map_eq_nil_iff] at h0
    apply hv.1
    rw [hv', h0, ← FreeGroup.one_eq_mk]
    group
  · intro l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
    exact toLetter_ne_none p
  · intro t
    simp only [List.get_eq_getElem, List.getElem_map, letterInv_toLetter]
    intro heq
    have heq := toLetter_injective heq
    have ht := t.2
    simp only [List.length_map] at ht
    by_cases h1 : t.val + 1 < R.length
    · have hm : (t.val + 1) % (R.map toLetter).length = t.val + 1 := by
        simp only [List.length_map]; exact Nat.mod_eq_of_lt h1
      simp only [hm] at heq
      have := hRc.isReduced.getElem t.val h1
      rw [heq] at this
      simp at this
    · have hn : t.val + 1 = R.length := by omega
      have hm : (t.val + 1) % (R.map toLetter).length = 0 := by
        simp only [List.length_map, hn, Nat.mod_self]
      simp only [hm] at heq
      have hlast : R.getLast? = some R[t.val] := by
        rw [List.getLast?_eq_getElem?]
        have e : R.length - 1 = t.val := by omega
        simp only [e]
        exact List.getElem?_eq_getElem _
      have hhead : R.head? = some R[0] := by
        rw [List.head?_eq_getElem?]; simp
      have := hRc.2 R[t.val] (by rw [hlast]; rfl) R[0] (by rw [hhead]; rfl)
      rw [heq] at this
      simp at this
  · rw [wordFree_map_toLetter, hv']
    group

end StrongConv.N52.PartW
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
/-! ## Part W: words and free groups -/
alias exists_cyc_rep := StrongConv.N52.PartW.exists_cyc_rep

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartW
/-! ## Powers and conjugation -/
lemma wordFree_append {d : ℕ} (a b : List (Letter d)) :
    wordFree (a ++ b) = wordFree a * wordFree b := by
  simp [wordFree]

lemma powList_succ {d : ℕ} (r : List (Letter d)) (k : ℕ) :
    powList r (k + 1) = r ++ powList r k := by
  simp [powList, List.replicate_succ]

lemma wordFree_powList {d : ℕ} (r : List (Letter d)) (k : ℕ) :
    wordFree (powList r k) = wordFree r ^ k := by
  induction k with
  | zero => simp [powList, wordFree]
  | succ k ih => rw [powList_succ, wordFree_append, ih, pow_succ']

lemma fixCount_conj {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    fixCount (ρ * π * ρ⁻¹) = fixCount π := by
  unfold fixCount
  refine card_bij' (fun x _ => ρ⁻¹ x) (fun y _ => ρ y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_filter] at hx ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := hx.2
    simp only [Equiv.Perm.mul_apply] at h
    conv_rhs => rw [← h]
    simp
  · intro y hy
    rw [mem_filter] at hy ⊢
    refine ⟨mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hy.2]
  · intro x _; simp
  · intro y _; simp

theorem fix_conj {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w r : List (Letter d))
    (v h : FreeGroup (Fin d)) (k : ℕ) (hw : wordFree w = v ^ k)
    (hr : wordFree r = h * v * h⁻¹) :
    fixCount (wordPerm σ w) = fixCount (wordPerm σ (powList r k)) := by
  rw [PartPerm.wordPerm_eq_lift, PartPerm.wordPerm_eq_lift, wordFree_powList, hr, hw,
    conj_pow, map_mul, map_mul, map_inv, map_pow, fixCount_conj]

end StrongConv.N52.PartW
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
alias fix_conj := StrongConv.N52.PartW.fix_conj

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartW
/-! ## Properties of `r ^ k` -/
lemma length_powList {d : ℕ} (r : List (Letter d)) (k : ℕ) :
    (powList r k).length = k * r.length := by
  induction k with
  | zero => simp [powList]
  | succ k ih => rw [powList_succ, List.length_append, ih]; ring

lemma getElem_powList {d : ℕ} (r : List (Letter d)) (k : ℕ) (t : ℕ)
    (ht : t < (powList r k).length) (hr : 0 < r.length) :
    (powList r k)[t] = r[t % r.length]'(Nat.mod_lt _ hr) := by
  induction k generalizing t with
  | zero => simp [powList] at ht
  | succ k ih =>
    simp only [powList_succ]
    rw [List.getElem_append]
    split_ifs with h
    · congr 1; exact (Nat.mod_eq_of_lt h).symm
    · have hlen := length_powList r (k + 1)
      have hlen' := length_powList r k
      rw [Nat.succ_mul] at hlen
      rw [ih (t - r.length) (by omega)]
      congr 1
      exact (Nat.mod_eq_sub_mod (by omega)).symm

theorem powList_props {d : ℕ} (r : List (Letter d)) (hne : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (k : ℕ) (hk : 1 ≤ k) :
    powList r k ≠ [] ∧ (∀ l ∈ powList r k, l ≠ none) ∧ CycRed (powList r k) := by
  have hr : 0 < r.length := List.length_pos_iff.2 hne
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.length_pos_iff, length_powList]
    exact Nat.mul_pos (by omega) hr
  · intro l hl
    simp only [powList, List.mem_flatten, List.mem_replicate] at hl
    obtain ⟨_, ⟨-, rfl⟩, hl⟩ := hl
    exact hnone l hl
  · intro t
    have ht := t.2
    have hL := length_powList r k
    simp only [List.get_eq_getElem]
    rw [getElem_powList _ _ _ _ hr, getElem_powList _ _ _ _ hr]
    have key := hcyc ⟨t.val % r.length, Nat.mod_lt _ hr⟩
    simp only [List.get_eq_getElem] at key
    have gen : ∀ m, r.length ∣ m →
        (t.val + 1) % m % r.length = (t.val % r.length + 1) % r.length := by
      intro m hm
      rw [Nat.mod_mod_of_dvd _ hm, Nat.add_mod]
      conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
    have hmod := gen _ (hL ▸ Dvd.intro_left k rfl)
    simp only [hmod]
    exact key

end StrongConv.N52.PartW
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
alias powList_props := StrongConv.N52.PartW.powList_props

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartW
/-! ## The expectation formula -/
theorem expect_formula {d : ℕ} (u : List (Letter d)) (N : ℕ) (_hN : 1 ≤ N) (hL : u.length ≤ N) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => (fixCount (wordPerm σ u) : ℝ)) =
      ∑ c ∈ CG u, (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (Es u c i).card : ℝ) := by
  have h1 : ∑ σ : Fin d → Equiv.Perm (Fin N), fixCount (wordPerm σ u) =
      ∑ c ∈ (univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c),
        if Good u c then N.descFactorial (nv c) * ∏ i, (N - (Es u c i).card).factorial
        else 0 := by
    rw [sum_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (u.length + 1) → Fin (u.length + 1) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (u.length + 1) → Fin N => canon x = c,
        G u N x = G u N c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact G_comp u (canon x) x (injOn_canon x) N
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, smul_eq_mul, G]
    split_ifs <;> simp
  unfold uniformExp
  rw [← Nat.cast_sum, h1, ← sum_filter]
  have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
    simp [Fintype.card_perm]
  rw [hcard, Nat.cast_sum, sum_div]
  unfold CG
  refine sum_congr rfl fun c _ => ?_
  have he : ∀ i, (Es u c i).card ≤ N := fun i =>
    (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans
      ((sum_card_Es_le u c).trans hL)
  have hfac : (N.factorial : ℝ) ^ d =
      (∏ i, (N.descFactorial (Es u c i).card : ℝ)) *
        ∏ i, ((N - (Es u c i).card).factorial : ℝ) := by
    rw [← prod_mul_distrib,
      show (N.factorial : ℝ) ^ d = ∏ _i : Fin d, (N.factorial : ℝ) by simp]
    refine prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [hfac, mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun i _ => by positivity)]

end StrongConv.N52.PartW
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
alias expect_formula := StrongConv.N52.PartW.expect_formula

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
variable {d : ℕ} {α : Type*} [DecidableEq α]
/-- The labelled edge of step `t`. -/
def ee (a : ℕ → Letter d) (x : ℕ → α) (t : ℕ) : Option (Fin d) × (α × α) :=
  (lab (a t), edge (a t) (x t) (x (t + 1)))

/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The labelled edges of steps `< k`. -/
def EE (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Finset (Option (Fin d) × (α × α)) :=
  (range k).image (ee a x)

/-- Step `k` is a closing step. -/
def closing (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Prop :=
  x (k + 1) ∈ UU x k ∧ ee a x k ∉ EE a x k

instance (a : ℕ → Letter d) (x : ℕ → α) : DecidablePred (closing a x) := by
  intro k; unfold closing; infer_instance

lemma mem_UU {x : ℕ → α} {k j : ℕ} (h : j ≤ k) : x j ∈ UU x k :=
  mem_image_of_mem _ (mem_range.2 (by omega))

lemma UU_succ (x : ℕ → α) (k : ℕ) : UU x (k + 1) = insert (x (k + 1)) (UU x k) := by
  simp [UU, range_add_one, image_insert]

lemma EE_succ (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) :
    EE a x (k + 1) = insert (ee a x k) (EE a x k) := by
  simp [EE, range_add_one, image_insert]

omit [DecidableEq α] in
lemma ee_eq {a : ℕ → Letter d} {x : ℕ → α} {s t : ℕ} (hs : a s ≠ none) (ht : a t ≠ none)
    (h : ee a x s = ee a x t) :
    (a t = a s ∧ x t = x s ∧ x (t + 1) = x (s + 1)) ∨
      (a t = letterInv (a s) ∧ x t = x (s + 1) ∧ x (t + 1) = x s) := by
  unfold ee at h
  generalize a s = l1 at *
  generalize a t = l2 at *
  rcases l1 with _ | i | i <;> rcases l2 with _ | j | j <;>
    simp_all [lab, edge, letterInv, Prod.ext_iff]

lemma EE_end {a : ℕ → Letter d} {x : ℕ → α} {k : ℕ} {p : Option (Fin d) × (α × α)}
    (hp : p ∈ EE a x k) : p.2.1 ∈ UU x k ∧ p.2.2 ∈ UU x k := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
  have hs := mem_range.1 hs
  have h1 : x s ∈ UU x k := mem_UU (by omega)
  have h2 : x (s + 1) ∈ UU x k := mem_UU (by omega)
  rcases edge_cases (a s) (x s) (x (s + 1)) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    simp only [ee, e1, e2]
  exacts [⟨h1, h2⟩, ⟨h2, h1⟩]

lemma count (a : ℕ → Letter d) (x : ℕ → α) :
    ∀ k, (UU x k).card + ((range k).filter (closing a x)).card = (EE a x k).card + 1
  | 0 => by simp [UU, EE]
  | k + 1 => by
      have ih := count a x k
      rw [UU_succ, EE_succ, range_add_one, filter_insert]
      have hk : k ∉ range k := by simp
      by_cases hx : x (k + 1) ∈ UU x k
      · by_cases he : ee a x k ∈ EE a x k
        · have hc : ¬ closing a x k := fun h => h.2 he
          rw [if_neg hc, insert_eq_of_mem hx, insert_eq_of_mem he]; exact ih
        · have hc : closing a x k := ⟨hx, he⟩
          rw [if_pos hc, insert_eq_of_mem hx, card_insert_of_notMem he,
            card_insert_of_notMem (fun h => hk (mem_filter.1 h).1)]
          omega
      · have he : ee a x k ∉ EE a x k := by
          intro h
          have := EE_end h
          rcases edge_cases (a k) (x k) (x (k + 1)) with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact hx (by simpa [ee, e2] using this.2)
          · exact hx (by simpa [ee, e1] using this.1)
        have hc : ¬ closing a x k := fun h => hx h.1
        rw [if_neg hc, card_insert_of_notMem hx, card_insert_of_notMem he]
        omega

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
variable {d : ℕ} {α : Type*} [DecidableEq α]
variable {L : ℕ} {a : ℕ → Letter d} {x : ℕ → α}
lemma step0 (h : ¬ closing a x 0) : x 1 ∉ UU x 0 := by
  intro hx
  exact h ⟨hx, by simp [EE]⟩

lemma step_new (hnone : ∀ t < L, a t ≠ none)
    (hcr : ∀ t, t + 1 < L → a (t + 1) ≠ letterInv (a t))
    {t : ℕ} (ht1 : 1 ≤ t) (htL : t < L) (hnew : x t ∉ UU x (t - 1)) (hnc : ¬ closing a x t) :
    x (t + 1) ∉ UU x t := by
  intro hin
  have he : ee a x t ∈ EE a x t := by
    by_contra h; exact hnc ⟨hin, h⟩
  obtain ⟨s, hs, hse⟩ := mem_image.1 he
  have hs := mem_range.1 hs
  rcases ee_eq (hnone s (by omega)) (hnone t htL) hse with ⟨-, h2, -⟩ | ⟨h1, h2, -⟩
  · exact hnew (h2 ▸ mem_UU (by omega))
  · by_cases hst : s + 1 ≤ t - 1
    · exact hnew (h2 ▸ mem_UU hst)
    · have : s = t - 1 := by omega
      subst this
      exact hcr (t - 1) (by omega) (by rw [show t - 1 + 1 = t by omega]; exact h1)

lemma chain (hnone : ∀ t < L, a t ≠ none)
    (hcr : ∀ t, t + 1 < L → a (t + 1) ≠ letterInv (a t))
    {t0 : ℕ} (h1 : 1 ≤ t0) (hnew : x t0 ∉ UU x (t0 - 1)) :
    ∀ t1, t0 ≤ t1 → t1 ≤ L → (∀ j, t0 ≤ j → j < t1 → ¬ closing a x j) →
      x t1 ∉ UU x (t1 - 1) := by
  intro t1 h01
  induction t1, h01 using Nat.le_induction with
  | base => intro _ _; exact hnew
  | succ t1 h0t ih =>
    intro hL hnc
    have := step_new hnone hcr (by omega) (by omega) (ih (by omega)
      (fun j hj hj' => hnc j hj (by omega))) (hnc t1 h0t (by omega))
    simpa using this

lemma hcr_lin (hcr : ∀ t < L, a ((t + 1) % L) ≠ letterInv (a t)) :
    ∀ t, t + 1 < L → a (t + 1) ≠ letterInv (a t) := by
  intro t ht
  have := hcr t (by omega)
  rwa [Nat.mod_eq_of_lt ht] at this

theorem gen_le (hL : 1 ≤ L) (hnone : ∀ t < L, a t ≠ none)
    (hcr : ∀ t < L, a ((t + 1) % L) ≠ letterInv (a t)) (hcl : x L = x 0) :
    (UU x L).card ≤ (EE a x L).card := by
  have hc := count a x L
  suffices h : ((range L).filter (closing a x)).card ≠ 0 by omega
  intro h0
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  have hnc : ∀ j, j < L → ¬ closing a x j := fun j hj => h0 (mem_range.2 hj)
  have hx1 := step0 (hnc 0 (by omega))
  have := chain hnone (hcr_lin hcr) (le_refl 1) hx1 L hL le_rfl (fun j _ hj => hnc j hj)
  exact this (hcl ▸ mem_UU (Nat.zero_le _))

omit [DecidableEq α] in
lemma letterInv_inv (l : Letter d) : letterInv (letterInv l) = l := by
  rcases l with _ | i | i <;> rfl

omit [DecidableEq α] in
lemma mod_succ_inj {M j jj : ℕ} (hj : j < M) (hjj : jj < M) (h : (j + 1) % M = (jj + 1) % M) :
    j = jj := by
  rcases Nat.lt_or_ge (j + 1) M with h1 | h1 <;> rcases Nat.lt_or_ge (jj + 1) M with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show jj + 1 = M by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show j + 1 = M by omega, Nat.mod_self] at h; omega
  · omega

theorem gen_struct (hL : 1 ≤ L) (hnone : ∀ t < L, a t ≠ none)
    (hcr : ∀ t < L, a ((t + 1) % L) ≠ letterInv (a t)) (hcl : x L = x 0)
    (hVE : (UU x L).card = (EE a x L).card) :
    ∃ M, 1 ≤ M ∧ M ∣ L ∧ (∀ t < L, a t = a (t % M)) ∧
      ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M) := by
  have hcl' := hcr_lin hcr
  have hc := count a x L
  obtain ⟨ts, hts⟩ := card_eq_one.1 (show ((range L).filter (closing a x)).card = 1 by omega)
  have htsL : ts < L := mem_range.1 (mem_filter.1 (hts ▸ mem_singleton_self ts)).1
  have hcts : closing a x ts := (mem_filter.1 (hts ▸ mem_singleton_self ts)).2
  have huniq : ∀ j < L, closing a x j → j = ts := fun j hj hcj =>
    mem_singleton.1 (hts ▸ mem_filter.2 ⟨mem_range.2 hj, hcj⟩)
  set M := ts + 1 with hMdef
  have hnewj : ∀ j, 1 ≤ j → j < M → x j ∉ UU x (j - 1) := by
    intro j hj1 hjM
    have h0 : ¬ closing a x 0 := fun h => by have := huniq 0 (by omega) h; omega
    exact chain hnone hcl' (le_refl 1) (step0 h0) j hj1 (by omega)
      (fun i hi hij hcl2 => by have := huniq i (by omega) hcl2; omega)
  have hD : ∀ i j, i < M → j < M → x i = x j → i = j := by
    intro i j hi hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hnewj j (by omega) hj (hij ▸ mem_UU (by omega))
    · exact hnewj i (by omega) hi (hij ▸ mem_UU (by omega))
  have hafter : ∀ t, M ≤ t → t < L → x (t + 1) ∈ UU x t := by
    intro t ht1 ht2
    by_contra hn
    exact chain hnone hcl' (show 1 ≤ t + 1 by omega) (by simpa using hn) L (by omega) le_rfl
      (fun j hj hj2 hcj => by have := huniq j hj2 hcj; omega)
      (show x L ∈ UU x (L - 1) by rw [hcl]; exact mem_UU (Nat.zero_le _))
  have hrep : ∀ t, M ≤ t → t < L → ee a x t ∈ EE a x t := by
    intro t ht1 ht2
    by_contra h
    have := huniq t ht2 ⟨hafter t ht1 ht2, h⟩
    omega
  have hback : ∀ t, t < L → ∃ j < M, ee a x t = ee a x j := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htL
      by_cases htM : t < M
      · exact ⟨t, htM, rfl⟩
      · obtain ⟨s, hs, hse⟩ := mem_image.1 (hrep t (by omega) htL)
        have hs := mem_range.1 hs
        obtain ⟨j, hj, hje⟩ := ih s hs (by omega)
        exact ⟨j, hj, hse.symm.trans hje⟩
  have hM0 : x M = x 0 := by
    obtain ⟨s, hs, hse⟩ := mem_image.1 hcts.1
    have hs := mem_range.1 hs
    by_cases hs0 : s = 0
    · subst hs0; exact hse.symm
    exfalso
    by_cases hML : M = L
    · have : x s = x 0 := by rw [hse, show ts + 1 = L from hML, hcl]
      exact hs0 (hD s 0 (by omega) (by omega) this)
    · obtain ⟨j, hj, hje⟩ := hback (L - 1) (by omega)
      have hL1 : L - 1 + 1 = L := by omega
      rcases ee_eq (hnone j (by omega)) (hnone (L - 1) (by omega)) hje.symm with
        ⟨-, -, h3⟩ | ⟨h1, -, h3⟩
      · rw [hL1, hcl] at h3
        by_cases hjM : j + 1 < M
        · have := hD 0 (j + 1) (by omega) hjM h3; omega
        · have : j + 1 = M := by omega
          rw [this, hMdef, ← hse] at h3
          exact hs0 (hD 0 s (by omega) (by omega) h3).symm
      · rw [hL1, hcl] at h3
        have hj0 : j = 0 := (hD 0 j (by omega) hj h3).symm
        subst hj0
        apply hcr (L - 1) (by omega)
        rw [hL1, Nat.mod_self, h1, letterInv_inv]
  have hxM : ∀ v ≤ M, x v = x (v % M) := by
    intro v hv
    rcases Nat.lt_or_ge v M with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show v = M by omega, Nat.mod_self, hM0]
  have hQ : ∀ t ≤ L, (∀ t' ≤ t, x t' = x (t' % M)) ∧ (∀ t' < t, a t' = a (t' % M)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨fun t' ht' => by simp [show t' = 0 by omega], fun _ h => absurd h (by omega)⟩
    | succ t ih =>
      intro htL
      obtain ⟨ihx, iha⟩ := ih (by omega)
      by_cases htM : t + 1 ≤ M
      · exact ⟨fun t' ht' => hxM t' (by omega), fun t' ht' => by rw [Nat.mod_eq_of_lt (by omega)]⟩
      · obtain ⟨j, hj, hje⟩ := hback t (by omega)
        have hi : t % M < M := Nat.mod_lt _ (by omega)
        have hxt := ihx t le_rfl
        rcases ee_eq (hnone j (by omega)) (hnone t (by omega)) hje.symm with
          ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · have hji : j = t % M := hD j (t % M) hj hi (h2.symm.trans hxt)
          have hat : a t = a (t % M) := hji ▸ h1
          have hxt1 : x (t + 1) = x ((t + 1) % M) := by
            rw [h3, hji, hxM (t % M + 1) (by omega), Nat.mod_add_mod]
          refine ⟨fun t' ht' => ?_, fun t' ht' => ?_⟩
          · rcases Nat.lt_or_ge t' (t + 1) with h | h
            · exact ihx t' (by omega)
            · rw [show t' = t + 1 by omega]; exact hxt1
          · rcases Nat.lt_or_ge t' t with h | h
            · exact iha t' h
            · rw [show t' = t by omega]; exact hat
        · exfalso
          have hjj : (t - 1) % M < M := Nat.mod_lt _ (by omega)
          have e1 : ((t - 1) % M + 1) % M = t % M := by
            rw [Nat.mod_add_mod, show t - 1 + 1 = t by omega]
          have e2 : (j + 1) % M = t % M := by
            apply hD _ _ (Nat.mod_lt _ (by omega)) hi
            rw [← hxM (j + 1) (by omega), ← hxt, h2]
          have hjeq : j = (t - 1) % M := mod_succ_inj hj hjj (e2.trans e1.symm)
          have ha1 : a (t - 1) = a j := by rw [hjeq]; exact iha (t - 1) (by omega)
          apply hcl' (t - 1) (by omega)
          rw [show t - 1 + 1 = t by omega, ha1]; exact h1
  obtain ⟨hQx, hQa⟩ := hQ L le_rfl
  have hDmod : ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M) := by
    intro u hu v hv
    rw [hQx u hu, hQx v hv]
    exact ⟨hD _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)), fun h => by rw [h]⟩
  refine ⟨M, by omega, Nat.dvd_of_mod_eq_zero ?_, hQa, hDmod⟩
  have := (hDmod L le_rfl 0 (by omega)).1 hcl
  simpa using this

omit [DecidableEq α] in
lemma mod_succ_iff {M s t : ℕ} : (s + 1) % M = (t + 1) % M ↔ s % M = t % M :=
  ⟨fun h => Nat.ModEq.add_right_cancel' 1 h, fun h => Nat.ModEq.add_right 1 h⟩

theorem gen_per (hnone : ∀ t < L, a t ≠ none)
    (hcr : ∀ t < L, a ((t + 1) % L) ≠ letterInv (a t))
    {M : ℕ} (hM : 1 ≤ M) (hML : M ∣ L) (hL : 1 ≤ L) (hper : ∀ t < L, a t = a (t % M))
    (hker : ∀ u ≤ L, ∀ v ≤ L, (x u = x v ↔ u % M = v % M)) :
    (∀ s < L, ∀ t < L, lab (a s) = lab (a t) →
      ((edge (a s) (x s) (x (s + 1))).1 = (edge (a t) (x t) (x (t + 1))).1 ↔
        (edge (a s) (x s) (x (s + 1))).2 = (edge (a t) (x t) (x (t + 1))).2)) ∧
    (UU x L).card = (EE a x L).card := by
  have hML' : M ≤ L := Nat.le_of_dvd (by omega) hML
  have CRM : ∀ s < L, ∀ t < L, t % M = (s + 1) % M → a t ≠ letterInv (a s) := by
    intro s hs t ht h heq
    have h1 := hcr (s % M) (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hML')
    have key : a ((s % M + 1) % L) = a t := by
      rw [hper _ (Nat.mod_lt _ (by omega)), Nat.mod_mod_of_dvd _ hML, Nat.mod_add_mod, ← h,
        ← hper t ht]
    rw [key, ← hper s hs] at h1
    exact h1 heq
  refine ⟨?_, ?_⟩
  · intro s hs t ht hlab
    have k1 := hker s (by omega) t (by omega)
    have k2 := hker (s + 1) (by omega) (t + 1) (by omega)
    have k3 := hker (s + 1) (by omega) t (by omega)
    have k4 := hker s (by omega) (t + 1) (by omega)
    have c1 := CRM s hs t ht
    have c2 := CRM t ht s hs
    rcases hs' : a s with _ | i | i <;> rcases ht' : a t with _ | j | j
    all_goals first
      | exact absurd hs' (hnone s hs)
      | exact absurd ht' (hnone t ht)
      | skip
    all_goals rw [hs', ht'] at hlab c1 c2
    all_goals simp only [lab, Option.some.injEq] at hlab
    all_goals subst hlab
    · simp only [edge]; rw [k2, k1, mod_succ_iff]
    · simp only [edge]
      refine iff_of_false (fun h => c1 ((k3.1 h).symm) rfl) (fun h => c2 ((k4.1 h)) rfl)
    · simp only [edge]
      refine iff_of_false (fun h => c2 ((k4.1 h)) rfl) (fun h => c1 ((k3.1 h).symm) rfl)
    · simp only [edge]; rw [k2, k1, mod_succ_iff]
  · have hcl : x L = x 0 := (hker L le_rfl 0 (by omega)).2 (by simp [Nat.mod_eq_zero_of_dvd hML])
    refine le_antisymm (gen_le hL hnone hcr hcl) (le_trans (b := M) ?_ ?_)
    · have hsub : EE a x L ⊆ (range M).image (ee a x) := by
        intro p hp
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
        have ht := mem_range.1 ht
        have hm : t % M < M := Nat.mod_lt _ (by omega)
        have hmt : t % M ≤ t := Nat.mod_le _ _
        refine mem_image.2 ⟨t % M, mem_range.2 hm, ?_⟩
        have e1 : x (t % M) = x t := (hker _ (by omega) t (by omega)).2 (Nat.mod_mod _ _)
        have e2 : x (t % M + 1) = x (t + 1) :=
          (hker _ (by omega) (t + 1) (by omega)).2 (by rw [Nat.mod_add_mod])
        simp only [ee, e1, e2, ← hper t ht]
      calc (EE a x L).card ≤ ((range M).image (ee a x)).card := card_le_card hsub
        _ ≤ (range M).card := card_image_le
        _ = M := card_range M
    · have hsub : (range M).image x ⊆ UU x L := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hy
        exact mem_UU (by have := mem_range.1 ht; omega)
      calc M = (range M).card := (card_range M).symm
        _ = ((range M).image x).card := by
          refine (card_image_of_injOn fun i hi j hj hij => ?_).symm
          have hi := mem_range.1 hi
          have hj := mem_range.1 hj
          have := (hker i (by omega) j (by omega)).1 hij
          rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
        _ ≤ (UU x L).card := card_le_card hsub

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
variable {d : ℕ}
/-- The letters of a word, `none` past its end. -/
def A (u : List (Letter d)) (t : ℕ) : Letter d := u.getD t none

/-- A colouring read along `ℕ`. -/
def X {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : ℕ) : β := c ⟨min t L, by omega⟩

lemma get_A (u : List (Letter d)) (t : Fin u.length) : u.get t = A u t.val := by
  simp [A]

lemma X_cs {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin L) :
    c t.castSucc = X c t.val := by
  unfold X; congr 1; ext; simp

lemma X_succ {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin L) :
    c t.succ = X c (t.val + 1) := by
  unfold X; congr 1; ext; simp

lemma X_fin {L : ℕ} {β : Type*} (c : Fin (L + 1) → β) (t : Fin (L + 1)) :
    c t = X c t.val := by
  unfold X; congr 1; ext; simp; omega

lemma lab_ne_none {l : Letter d} (h : l ≠ none) : lab l ≠ none := by
  rcases l with _ | i | i <;> simp_all [lab]

lemma mem_Es {β : Type*} [DecidableEq β] (u : List (Letter d)) (c : Fin (u.length + 1) → β)
    (i : Fin d) (p : β × β) :
    p ∈ Es u c i ↔ ∃ t < u.length, lab (A u t) = some i ∧
      edge (A u t) (X c t) (X c (t + 1)) = p := by
  unfold Es
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.val, t.2, by rwa [← get_A], by rw [get_A, X_cs c, X_succ c]⟩
  · rintro ⟨t, ht, hl, rfl⟩
    refine ⟨⟨t, ht⟩, by rwa [get_A], ?_⟩
    rw [get_A, X_cs c, X_succ c]

lemma nv_eq {L : ℕ} {β : Type*} [DecidableEq β] (c : Fin (L + 1) → β) :
    nv c = (UU (X c) L).card := by
  unfold nv UU
  congr 1
  ext y
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t.val, t.2, (X_fin c t).symm⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨min t L, by omega⟩, rfl⟩

lemma Ecount_eq (u : List (Letter d)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (hnone : ∀ t < u.length, A u t ≠ none) :
    Ecount u c = (EE (A u) (X c) u.length).card := by
  have h : EE (A u) (X c) u.length =
      univ.biUnion (fun i => (Es u c i).image (fun p => (some i, p))) := by
    ext ⟨o, p⟩
    simp only [EE, mem_image, mem_range, mem_biUnion, mem_univ, true_and, ee, Prod.mk.injEq,
      mem_Es]
    constructor
    · rintro ⟨t, ht, ho, hp⟩
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (lab_ne_none (hnone t ht))
      exact ⟨i, p, ⟨t, ht, hi, hp⟩, by rw [← ho, hi], rfl⟩
    · rintro ⟨i, q, ⟨t, ht, hi, rfl⟩, rfl, rfl⟩
      exact ⟨t, ht, hi, rfl⟩
  rw [h, card_biUnion]
  · unfold Ecount
    refine sum_congr rfl fun i _ => (card_image_of_injective _ (fun p q h => ?_)).symm
    simpa using h
  · intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro z hz hz'
    obtain ⟨p, -, rfl⟩ := mem_image.1 hz
    obtain ⟨q, -, h⟩ := mem_image.1 hz'
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact hij h.1.symm

lemma hcl_of_good (u : List (Letter d)) (c : Fin (u.length + 1) → Fin (u.length + 1))
    (h : Good u c) : X c u.length = X c 0 := by
  have := h.2.2
  rw [X_fin c 0, X_fin c (Fin.last _)] at this
  simpa using this.symm

lemma hcr_of (u : List (Letter d)) (h : CycRed u) :
    ∀ t < u.length, A u ((t + 1) % u.length) ≠ letterInv (A u t) := by
  intro t ht
  have := h ⟨t, ht⟩
  rw [get_A, get_A] at this
  exact this

lemma hnone_of (u : List (Letter d)) (h : ∀ l ∈ u, l ≠ none) : ∀ t < u.length, A u t ≠ none := by
  intro t ht
  rw [A, List.getD_eq_getElem _ _ ht]
  exact h _ (List.getElem_mem ht)

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
theorem nv_le_Ecount {d : ℕ} (u : List (Letter d)) (hne : u ≠ []) (hnone : ∀ l ∈ u, l ≠ none)
    (hcyc : CycRed u) (c : Fin (u.length + 1) → Fin (u.length + 1)) (hc : c ∈ CG u) :
    nv c ≤ Ecount u c := by
  have hc' := (mem_filter.1 hc).2
  rw [nv_eq, Ecount_eq u c (hnone_of u hnone)]
  exact gen_le (List.length_pos_iff.2 hne) (hnone_of u hnone) (hcr_of u hcyc)
    (hcl_of_good u c hc')

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
/-! ## Part G: the colourings -/
alias nv_le_Ecount := StrongConv.N52.PartG.nv_le_Ecount

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
variable {d : ℕ}
/-- The periodic colouring `t ↦ t mod M`. -/
def col (L M : ℕ) : Fin (L + 1) → Fin (L + 1) :=
  fun t => ⟨t.val % M, lt_of_le_of_lt (Nat.mod_le _ _) t.2⟩

lemma canon_col (L M : ℕ) : canon (col L M) = col L M := by
  funext t
  unfold canon
  apply le_antisymm
  · apply Finset.min'_le
    simp [col]
  · apply Finset.le_min'
    intro y hy
    simp only [mem_filter, mem_univ, true_and, col, Fin.mk.injEq] at hy
    rw [Fin.le_iff_val_le_val]
    show t.val % M ≤ y.val
    rw [← hy]; exact Nat.mod_le _ _

lemma col_ne {L M M' : ℕ} (hM : 1 ≤ M) (hlt : M < M') (hML : M ≤ L) : col L M ≠ col L M' := by
  intro h
  have := congrArg Fin.val (congrFun h ⟨M, by omega⟩)
  simp only [col, Nat.mod_self, Nat.mod_eq_of_lt hlt] at this
  omega

lemma getD_flat {β : Type*} (s : List β) (dflt : β) (hs : s ≠ []) :
    ∀ j t, t < j * s.length →
      ((List.replicate j s).flatten).getD t dflt = s.getD (t % s.length) dflt
  | 0, t, h => by simp at h
  | j + 1, t, h => by
      rw [List.replicate_succ, List.flatten_cons]
      by_cases ht : t < s.length
      · rw [List.getD_append _ _ _ _ ht, Nat.mod_eq_of_lt ht]
      · rw [Nat.succ_mul] at h
        rw [List.getD_append_right _ _ _ _ (by omega), getD_flat s dflt hs j _ (by omega)]
        congr 1
        conv_rhs => rw [show t = t - s.length + s.length by omega]
        rw [Nat.add_mod_right]

lemma length_powList (r : List (Letter d)) (k : ℕ) : (powList r k).length = k * r.length := by
  simp [powList, List.length_flatten, List.map_replicate, List.sum_replicate]

lemma A_pow (r : List (Letter d)) (hne : r ≠ []) (k t : ℕ) (ht : t < k * r.length) :
    A (powList r k) t = A r (t % r.length) :=
  getD_flat r none hne k t ht

lemma wordFree_append (l1 l2 : List (Letter d)) :
    wordFree (l1 ++ l2) = wordFree l1 * wordFree l2 := by
  unfold wordFree; rw [List.map_append, List.prod_append]

lemma wordFree_flat (s : List (Letter d)) : ∀ j,
    wordFree ((List.replicate j s).flatten) = wordFree s ^ j
  | 0 => by simp [wordFree]
  | j + 1 => by
      rw [List.replicate_succ, List.flatten_cons, wordFree_append, wordFree_flat s j, pow_succ']

/-- `p` is a period of `f`. -/
def IsPer {β : Type*} (f : ℕ → β) (p : ℕ) : Prop := ∀ t, f (t + p) = f t

lemma per_mul {β : Type*} {f : ℕ → β} {p : ℕ} (h : IsPer f p) : ∀ m, IsPer f (p * m)
  | 0 => fun t => by simp
  | m + 1 => fun t => by
      rw [Nat.mul_succ, ← add_assoc, h, per_mul h m t]

lemma per_sub {β : Type*} {f : ℕ → β} {p q : ℕ} (hp : IsPer f p) (hq : IsPer f q) (hqp : q ≤ p) :
    IsPer f (p - q) := fun t => by
  rw [← hq (t + (p - q)), add_assoc, Nat.sub_add_cancel hqp, hp]

lemma per_gcd {β : Type*} (f : ℕ → β) (m n : ℕ) : IsPer f m → IsPer f n → IsPer f (Nat.gcd m n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n hm ih =>
    intro hpm hpn
    rw [Nat.gcd_rec]
    apply ih _ hpm
    have e : n % m = n - m * (n / m) := by
      have := Nat.div_add_mod n m; omega
    rw [e]
    exact per_sub hpn (per_mul hpm _) (Nat.mul_div_le n m)

lemma A_take (r : List (Letter d)) {g j : ℕ} (hj : j < g) : A (r.take g) j = A r j := by
  unfold A
  simp [List.getD_eq_getElem?_getD, hj]

lemma per_dvd (r : List (Letter d)) (hne : r ≠ []) (hnp : IsNonPower (wordFree r)) (k : ℕ)
    (hk : 1 ≤ k) (M : ℕ) (hM : 1 ≤ M) (hML : M ∣ k * r.length)
    (hper : ∀ t < k * r.length, A (powList r k) t = A (powList r k) (t % M)) :
    r.length ∣ M := by
  have hn0 : 0 < r.length := List.length_pos_iff.2 hne
  have hL0 : 0 < k * r.length := Nat.mul_pos (by omega) hn0
  have hnL : r.length ∣ k * r.length := Dvd.intro_left k rfl
  let f : ℕ → Letter d := fun t => A r (t % r.length)
  have hfL : ∀ t, f t = A (powList r k) (t % (k * r.length)) := by
    intro t
    rw [A_pow r hne k _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hnL]
  have hfM : ∀ t, f t = A (powList r k) (t % M) := by
    intro t; rw [hfL, hper _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hML]
  have pn : IsPer f r.length := fun t => by simp only [f, Nat.add_mod_right]
  have pM : IsPer f M := fun t => by rw [hfM, hfM, Nat.add_mod_right]
  have pg := per_gcd f M r.length pM pn
  set g := Nat.gcd M r.length with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgn : g ∣ r.length := Nat.gcd_dvd_right M r.length
  have hgle : g ≤ r.length := Nat.le_of_dvd hn0 hgn
  have hrt : ∀ t < r.length, A r t = A r (t % g) := by
    intro t ht
    have h1 : f t = A r t := by simp only [f, Nat.mod_eq_of_lt ht]
    have h2 : f (t % g) = A r (t % g) := by
      simp only [f, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) ht)]
    rw [← h1, ← h2]
    conv_lhs => rw [← Nat.mod_add_div t g]
    exact per_mul pg (t / g) (t % g)
  have htk : (r.take g).length = g := by simp [hgle]
  have htk0 : r.take g ≠ [] := by
    intro h; rw [h] at htk; simp at htk; omega
  have hreq : r = (List.replicate (r.length / g) (r.take g)).flatten := by
    have hlen : ((List.replicate (r.length / g) (r.take g)).flatten).length = r.length := by
      simp [List.length_flatten, List.map_replicate, List.sum_replicate, htk,
        Nat.div_mul_cancel hgn]
    apply List.ext_getElem hlen.symm
    intro t h1 h2
    rw [← List.getD_eq_getElem _ none h1, ← List.getD_eq_getElem _ none h2,
      getD_flat _ none htk0 _ t (by rw [htk, Nat.div_mul_cancel hgn]; exact h1), htk]
    show A r t = A (r.take g) (t % g)
    rw [A_take r (Nat.mod_lt _ hg0)]
    exact hrt t h1
  have hw : wordFree r = wordFree (r.take g) ^ (r.length / g) := by
    conv_lhs => rw [hreq]
    exact wordFree_flat _ _
  have h1 : r.length / g < 2 := by
    by_contra h
    exact hnp.2 _ _ (by omega) hw
  have h2 : 0 < r.length / g := Nat.div_pos hgle hg0
  have h3 : r.length = g := by
    have := Nat.div_mul_cancel hgn
    rw [show r.length / g = 1 by omega, one_mul] at this
    exact this.symm
  rw [h3]
  exact Nat.gcd_dvd_left M r.length

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG
theorem card_eq_divisors {d : ℕ} (r : List (Letter d)) (hne : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (k : ℕ) (hk : 1 ≤ k) :
    ((CG (powList r k)).filter fun c => nv c = Ecount (powList r k) c).card = k.divisors.card := by
  have hn0 : 0 < r.length := List.length_pos_iff.2 hne
  have hlen : (powList r k).length = k * r.length := length_powList r k
  have hL : 1 ≤ (powList r k).length := by rw [hlen]; exact Nat.mul_pos hk hn0
  have hnL : r.length ∣ (powList r k).length := hlen ▸ Dvd.intro_left k rfl
  have hA : ∀ t < (powList r k).length, A (powList r k) t = A r (t % r.length) :=
    fun t ht => A_pow r hne k t (hlen ▸ ht)
  have hnoneA : ∀ t < (powList r k).length, A (powList r k) t ≠ none := by
    intro t ht
    rw [hA t ht]
    exact hnone_of r hnone _ (Nat.mod_lt _ hn0)
  have hcrA : ∀ t < (powList r k).length,
      A (powList r k) ((t + 1) % (powList r k).length) ≠ letterInv (A (powList r k) t) := by
    intro t ht
    rw [hA _ (Nat.mod_lt _ (by omega)), hA t ht, Nat.mod_mod_of_dvd _ hnL]
    have := hcr_of r hcyc (t % r.length) (Nat.mod_lt _ hn0)
    rwa [Nat.mod_add_mod] at this
  have hS : (CG (powList r k)).filter (fun c => nv c = Ecount (powList r k) c) =
      k.divisors.image (fun a => col (powList r k).length (r.length * a)) := by
    ext c
    simp only [mem_filter, mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hc, hVE⟩
      have hc' := mem_filter.1 hc
      have hcan : canon c = c := (mem_filter.1 hc'.1).2
      rw [nv_eq, Ecount_eq _ c hnoneA] at hVE
      obtain ⟨M, hM, hML, hper, hker⟩ :=
        gen_struct hL hnoneA hcrA (hcl_of_good _ c hc'.2) hVE
      obtain ⟨a, rfl⟩ := per_dvd r hne hnp k hk M hM (hlen ▸ hML) (fun t ht => hper t (hlen ▸ ht))
      refine ⟨a, ⟨?_, by omega⟩, ?_⟩
      · rw [hlen, mul_comm k] at hML
        exact Nat.dvd_of_mul_dvd_mul_left hn0 hML
      · calc col _ (r.length * a) = canon (col _ (r.length * a)) := (canon_col _ _).symm
          _ = canon c := by
            refine canon_eq_of_ker _ _ fun s t => ?_
            rw [X_fin c s, X_fin c t, hker s.val (by omega) t.val (by omega), Fin.ext_iff]
            rfl
          _ = c := hcan
    · rintro ⟨a, ⟨hak, hk0⟩, rfl⟩
      have ha : 1 ≤ a := Nat.pos_of_dvd_of_pos hak (by omega)
      have hM : 1 ≤ r.length * a := Nat.mul_pos hn0 ha
      have hML : r.length * a ∣ (powList r k).length := by
        rw [hlen, mul_comm k]; exact Nat.mul_dvd_mul_left _ hak
      have hper : ∀ t < (powList r k).length,
          A (powList r k) t = A (powList r k) (t % (r.length * a)) := by
        intro t ht
        rw [hA t ht, hA _ (lt_of_le_of_lt (Nat.mod_le _ _) ht),
          Nat.mod_mod_of_dvd _ (Dvd.intro a rfl)]
      have hker : ∀ s ≤ (powList r k).length, ∀ t ≤ (powList r k).length,
          (X (col (powList r k).length (r.length * a)) s =
            X (col (powList r k).length (r.length * a)) t ↔
              s % (r.length * a) = t % (r.length * a)) := by
        intro s hs t ht
        simp [X, col, Fin.ext_iff, min_eq_left hs, min_eq_left ht]
      obtain ⟨hfold, hcard⟩ := gen_per hnoneA hcrA hM hML hL hper hker
      have hgood : Good (powList r k) (col (powList r k).length (r.length * a)) := by
        unfold Good
        refine ⟨fun t ht => absurd ht (by rw [get_A]; exact hnoneA t.val t.2),
          fun i p hp q hq => ?_, ?_⟩
        · rw [mem_Es] at hp hq
          obtain ⟨s, hs, hls, rfl⟩ := hp
          obtain ⟨t, ht, hlt, rfl⟩ := hq
          exact hfold s hs t ht (hls.trans hlt.symm)
        · ext; simp [col, Nat.mod_eq_zero_of_dvd hML]
      refine ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, canon_col _ _⟩, hgood⟩, ?_⟩
      rw [nv_eq, Ecount_eq _ _ hnoneA]
      exact hcard
  rw [hS, card_image_of_injOn]
  intro a ha b hb hab
  simp only [mem_coe, Nat.mem_divisors] at ha hb
  have hle : ∀ c, c ∣ k → r.length * c ≤ (powList r k).length := fun c hc => by
    rw [hlen, mul_comm k]; exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (by omega) hc)
  by_contra hne'
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · exact col_ne (Nat.mul_pos hn0 (Nat.pos_of_dvd_of_pos ha.1 (by omega)))
      (Nat.mul_lt_mul_of_pos_left h hn0) (hle a ha.1) hab
  · exact col_ne (Nat.mul_pos hn0 (Nat.pos_of_dvd_of_pos hb.1 (by omega)))
      (Nat.mul_lt_mul_of_pos_left h hn0) (hle b hb.1) hab.symm

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
alias card_eq_divisors := StrongConv.N52.PartG.card_eq_divisors

end StrongConv.N52
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartM
/-- `N^{(m)} / N^m → 1`. -/
lemma tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial m : ℝ) / (N : ℝ) ^ m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ∏ j ∈ range m, (1 - (j : ℝ) / N)) atTop
      (𝓝 (∏ j ∈ range m, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun j _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  simp only [sub_zero, prod_const_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with N hN
  have hNm : m ≤ N := le_of_max_le_left hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := le_of_max_le_right hN
    exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_div_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj : j < m := mem_range.1 hj
  rw [Nat.cast_sub (by omega), sub_div, div_self hN0]

/-- `N^a / N^b → [a = b]` for `a ≤ b`. -/
lemma tendsto_pow_div_pow (a b : ℕ) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / (N : ℝ) ^ b) atTop (𝓝 (if a = b then 1 else 0)) := by
  split_ifs with h
  · subst h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [div_self (pow_ne_zero _ hN0)]
  · have h1 : Tendsto (fun N : ℕ => ((N : ℝ) ^ (b - a))⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by omega : b - a ≠ 0)).comp
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [pow_sub₀ _ hN0 hab]
    field_simp

lemma tendsto_term {ι : Type*} [Fintype ι] (a : ℕ) (b : ι → ℕ) (hab : a ≤ ∑ i, b i) :
    Tendsto (fun N : ℕ => (N.descFactorial a : ℝ) / ∏ i, (N.descFactorial (b i) : ℝ)) atTop
      (𝓝 (if a = ∑ i, b i then 1 else 0)) := by
  have hA := tendsto_descFactorial_div_pow a
  have hB : Tendsto (fun N : ℕ => ∏ i, (N.descFactorial (b i) : ℝ) / (N : ℝ) ^ (b i)) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd _ fun i _ => tendsto_descFactorial_div_pow (b i)
  rw [prod_const_one] at hB
  have hP := tendsto_pow_div_pow a (∑ i, b i) hab
  have h := (hA.div hB one_ne_zero).mul hP
  rw [div_one, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [prod_div_distrib, prod_pow_eq_pow_sum]
  by_cases hz : ∏ i, (N.descFactorial (b i) : ℝ) = 0
  · simp [hz]
  · field_simp

lemma uniformExp_sub_div {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (N : ℝ)
    (hN : N ≠ 0) :
    N * uniformExp (fun x => (f x - 1) / N) = uniformExp f - 1 := by
  unfold uniformExp
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  field_simp

theorem tendsto_mul_uniformExp_trN_wordEval (d : ℕ) (w : List (Letter d)) (hw : wordFree w ≠ 1)
    (v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k) (hwv : wordFree w = v ^ k) :
    Tendsto (fun N : ℕ => (N : ℝ) *
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)))
      atTop (𝓝 ((k.divisors.card : ℝ) - 1)) := by
  classical
  obtain ⟨r, h, hne, hnone, hcyc, hr⟩ := exists_cyc_rep v hv
  obtain ⟨une, unone, ucyc⟩ := powList_props r hne hnone hcyc k hk
  have hnp : IsNonPower (wordFree r) := by
    refine ⟨?_, fun x m hm hx => hv.2 (h⁻¹ * x * h) m hm ?_⟩
    · rw [hr]
      intro h1
      apply hv.1
      have := congrArg (fun g => h⁻¹ * g * h) h1
      simpa [mul_assoc] using this
    · rw [show h⁻¹ * x * h = h⁻¹ * x * h⁻¹⁻¹ by simp, conj_pow, ← hx, hr]
      group
  set u := powList r k with hu
  have hT : ∀ c ∈ CG u, Tendsto (fun N : ℕ =>
      (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (Es u c i).card : ℝ)) atTop
      (𝓝 (if nv c = Ecount u c then 1 else 0)) := fun c hc =>
    tendsto_term (nv c) (fun i => (Es u c i).card) (nv_le_Ecount u une unone ucyc c hc)
  have hsum := tendsto_finsetSum (CG u) hT
  rw [sum_boole, card_eq_divisors r hne hnone hcyc hnp k hk] at hsum
  refine (hsum.sub_const 1).congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 u.length)] with N hN
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNL : u.length ≤ N := le_of_max_le_right hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e1 : (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) =
      fun σ => ((fixCount (wordPerm σ u) : ℝ) - 1) / N := by
    funext σ
    rw [PartPerm.trN_wordEval_sModel, fix_conj σ w r v h k hwv hr]
  rw [e1, uniformExp_sub_div _ _ hN0, expect_formula u N hN1 hNL]

end StrongConv.N52.PartM
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb
noncomputable section
namespace StrongConv.N52
/-! ## Part M: assembly -/
alias tendsto_mul_uniformExp_trN_wordEval := StrongConv.N52.PartM.tendsto_mul_uniformExp_trN_wordEval

end StrongConv.N52
end
end

alias StrongConv.tendsto_mul_uniformExp_trN_wordEval_dev := StrongConv.N52.tendsto_mul_uniformExp_trN_wordEval

end
end

section
open Filter Topology
open StrongConv

theorem solution (d : ℕ) (w : List (Letter d)) (hw : wordFree w ≠ 1)
    (v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k) (hwv : wordFree w = v ^ k) :
    Tendsto (fun N : ℕ => (N : ℝ) *
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)))
      atTop (𝓝 ((k.divisors.card : ℝ) - 1)) := by
  apply StrongConv.tendsto_mul_uniformExp_trN_wordEval_dev <;> assumption

end
