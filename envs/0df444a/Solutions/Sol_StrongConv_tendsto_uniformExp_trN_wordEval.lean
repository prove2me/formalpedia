-- Prove2me | solution 1 for StrongConv.tendsto_uniformExp_trN_wordEval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:48:11.432512+00:00
-- url     : https://prove2.me/submissions/8b249a28-300e-41df-8120-307eac9d7c14

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_tendsto_mul_uniformExp_trN_wordEval
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


end StrongConv.S5
end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartRoot

open FreeGroup FreeGroup.reduceCyclically

lemma length_toWord_pow_ge {d : ℕ} (v : FreeGroup (Fin d)) (hv : v ≠ 1) (k : ℕ) :
    k ≤ (v ^ k).toWord.length := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hr : reduceCyclically v.toWord ≠ [] := by
    intro h
    apply hv
    have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
    rw [mk_toWord, h, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel] at this
    exact this.symm
  have hw : (v ^ k).toWord = conjugator v.toWord ++
      (List.replicate k (reduceCyclically v.toWord)).flatten ++ invRev (conjugator v.toWord) := by
    rw [toWord_pow, reduce_flatten_replicate isReduced_toWord, if_neg hk.ne']
  rw [hw]
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  have : 1 ≤ (reduceCyclically v.toWord).length := List.length_pos_iff.mpr hr
  nlinarith

theorem exists_nonpower_pow {d : ℕ} (g : FreeGroup (Fin d)) (hg : g ≠ 1) :
    ∃ (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v ∧ 1 ≤ k ∧ g = v ^ k := by
  classical
  let B := g.toWord.length
  let P : ℕ → Prop := fun k => ∃ v : FreeGroup (Fin d), g = v ^ k
  have hbound : ∀ k, P k → k ≤ B := by
    rintro k ⟨v, hv⟩
    have hv1 : v ≠ 1 := by rintro rfl; exact hg (by simpa using hv)
    have := length_toWord_pow_ge v hv1 k
    rw [← hv] at this
    exact this
  have hP1 : P 1 := ⟨g, by simp⟩
  have h1B : 1 ≤ B := hbound 1 hP1
  set k := Nat.findGreatest P B with hk
  have hPk : P k := Nat.findGreatest_spec h1B hP1
  have hk1 : 1 ≤ k := Nat.le_findGreatest h1B hP1
  obtain ⟨v, hv⟩ := hPk
  refine ⟨v, k, ⟨?_, ?_⟩, hk1, hv⟩
  · rintro rfl; exact hg (by simpa using hv)
  · intro u m hm hvu
    have hPkm : P (k * m) := ⟨u, by rw [hv, hvu, ← pow_mul, mul_comm]⟩
    have hle : k * m ≤ k := Nat.le_findGreatest (hbound _ hPkm) hPkm
    nlinarith

end StrongConv.S5.PartRoot

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

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]

theorem tau_wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    tau (wordEval (sLimit d) w) = if wordFree w = 1 then 1 else 0 := by
  classical
  rw [wordEval_sLimit, tau, delta, lp.inner_single_left, leftReg_apply]
  simp only [mul_one, lp.single_apply]
  by_cases h : wordFree w = 1
  · simp [h]
  · rw [if_neg h, Pi.single_apply, if_neg (by simpa [inv_eq_one] using h)]
    simp

end StrongConv.S5.PartPerm


end
section

open Polynomial Finset

noncomputable section

namespace StrongConv.S5.PartAlg

end StrongConv.S5.PartAlg

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

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

end Bounds

end StrongConv.S5.PartComb

end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

end StrongConv.S5

namespace StrongConv.S5

theorem uniformExp_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    uniformExp (fun _ : X => c) = c := by
  unfold uniformExp
  have hc : (Fintype.card X : ℝ) ≠ 0 := by positivity
  simp [Finset.sum_const, hc]

theorem cor53_real (d : ℕ) (w : List (Letter d))
    (lem52 : ∀ (hw : wordFree w ≠ 1) (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v → 1 ≤ k →
      wordFree w = v ^ k →
      Tendsto (fun N : ℕ => (N : ℝ) *
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)))
        atTop (𝓝 ((k.divisors.card : ℝ) - 1))) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (wordEval (sModel σ) w))) atTop (𝓝 (if wordFree w = 1 then 1 else 0)) := by
  by_cases h1 : wordFree w = 1
  · rw [if_pos h1]
    have : ∀ N : ℕ, uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (wordEval (sModel σ) w)) = ((N : ℝ) - 1) / N := by
      intro N
      haveI : Nonempty (Fin d → Equiv.Perm (Fin N)) := ⟨fun _ => 1⟩
      have : ∀ σ : Fin d → Equiv.Perm (Fin N), trN N (wordEval (sModel σ) w) = ((N : ℝ) - 1) / N := by
        intro σ
        rw [PartPerm.trN_wordEval_sModel, PartPerm.wordPerm_eq_lift, h1, map_one]
        simp [fixCount]
      simp only [this]
      exact uniformExp_const _
    simp only [this]
    have h2 : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [if_neg h1]
    obtain ⟨v, k, hv, hk, hwv⟩ := PartRoot.exists_nonpower_pow (wordFree w) h1
    have h5 := lem52 h1 v k hv hk hwv
    have h6 := h5.mul tendsto_one_div_atTop_nhds_zero_nat
    rw [mul_zero] at h6
    refine h6.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp

theorem cor53 (d : ℕ) (w : List (Letter d)) :
    Tendsto (fun N : ℕ => ((uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        trN N (wordEval (sModel σ) w)) : ℝ) : ℂ))
      atTop (𝓝 (tau (wordEval (sLimit d) w))) := by
  rw [PartPerm.tau_wordEval_sLimit]
  have := (Complex.continuous_ofReal.tendsto _).comp
    (cor53_real d w (fun hw v k hv hk hwv => tendsto_mul_uniformExp_trN_wordEval d w hw v k hv hk hwv))
  have h2 : ((if wordFree w = 1 then (1 : ℝ) else 0 : ℝ) : ℂ) = if wordFree w = 1 then 1 else 0 := by
    split_ifs <;> simp
  rw [← h2]
  exact this

end StrongConv.S5

end

open Filter Topology in
theorem solution (d : ℕ) (w : List (StrongConv.Letter d)) :
    Tendsto (fun N : ℕ => ((StrongConv.uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        StrongConv.trN N (StrongConv.wordEval (StrongConv.sModel σ) w)) : ℝ) : ℂ))
      atTop (𝓝 (StrongConv.tau (StrongConv.wordEval (StrongConv.sLimit d) w))) :=
  StrongConv.S5.cor53 d w
