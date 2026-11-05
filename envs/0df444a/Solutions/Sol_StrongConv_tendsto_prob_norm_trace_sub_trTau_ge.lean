-- Prove2me | solution 1 for StrongConv.tendsto_prob_norm_trace_sub_trTau_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:47:49.948931+00:00
-- url     : https://prove2.me/submissions/4350dd09-e40c-49cb-b53b-c9ebc6598140

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_uniformExp_trN_wordEval_eq_div
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
import Mathlib

section
section
section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (y : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T y a = ∑ b, A a b • T (y b) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.single_apply,
    PiLp.proj_apply, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_sum, WithLp.ofLp_smul,
    WithLp.ofLp_toLp, Pi.smul_apply, Pi.single_apply]
  simp [Finset.sum_comm (γ := Fin n)]

lemma inner_tensorOp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin m => H)) (y : PiLp 2 (fun _ : Fin n => H)) :
    ⟪x, tensorOp A T y⟫_ℂ = ∑ a, ∑ b, A a b * ⟪x a, T (y b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorOp_apply, inner_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right]

end StrongConv.Stable
end
end

section
open scoped InnerProductSpace
open Matrix

noncomputable section

namespace StrongConv.Stable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end StrongConv.Stable
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.Stable.Perm

open scoped InnerProductSpace

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

end StrongConv.Stable.Perm
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
/-- The free-group element of a word in `s, s*`: `sᵢ ↦ gᵢ`, `sᵢ* ↦ gᵢ⁻¹`. -/
def fw {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) : FreeGroup (Fin d) :=
  (w.toList.map fun
    | Sum.inl i => FreeGroup.of i
    | Sum.inr i => (FreeGroup.of i)⁻¹).prod

/-- The character `χ_N(g) = Tr π_N(g)`. -/
def chi (π : StableRep) (N : ℕ) (g : Equiv.Perm (Fin N)) : ℂ :=
  (π.π N g : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace

/-- Number of fixed points. -/
def fixc {N : ℕ} (g : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => g x = x).card

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartT
open scoped InnerProductSpace
/-! ### Traces of `tensorOp` -/
lemma trace_toEuclideanCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ ((Matrix.toEuclideanCLM (𝕜 := ℂ) M :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = M.trace := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

lemma trace_tensorOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((tensorOp A T : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
          PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  classical
  unfold tensorOp
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum,
    map_smul]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : ∀ b : Fin D,
      LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a).comp
            (T.comp (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H))))) :
              PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
        if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
    intro b
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp]
    have : (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H).comp
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a)).comp T) =
          if a = b then T else 0 := by
      ext x
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]
    split_ifs <;> simp
  simp only [key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.diag_apply]

/-! ### Words evaluated at the model -/
lemma wordOp_model (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
    (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp (π.model σ) w = Matrix.toEuclideanCLM (𝕜 := ℂ)
      (π.π N (FreeGroup.lift σ (StrongConv.Stable.A2.fw w)) :
        Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) := by
  unfold wordOp StrongConv.Stable.A2.fw
  generalize w.toList = L
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Submonoid.coe_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases l with i | i
    · simp [letterOp, StableRep.model]
    · simp only [letterOp, StableRep.model, ← map_star]
      congr 1
      simp

theorem trace_eval_model (π : StableRep) {D d N : ℕ} (P : NCPoly D d)
    (σ : Fin d → Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((P.eval (π.model σ) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) =
      ∑ w ∈ P.support, (P w).trace * chi π N (FreeGroup.lift σ (fw w)) := by
  unfold NCPoly.eval
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [trace_tensorOp, wordOp_model, trace_toEuclideanCLM]
  rfl

end StrongConv.Stable.A2.PartT
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
/-! ## Part T: trace algebra -/
alias trace_eval_model := StrongConv.Stable.A2.PartT.trace_eval_model

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartT
open scoped InnerProductSpace
/-! ### The limit model -/
lemma wordOp_eq_wordEval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u w = wordEval u (w.toList.map some) := by
  unfold wordOp wordEval
  rw [List.map_map]
  rfl

lemma fw_eq_wordFree {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    StrongConv.Stable.A2.fw w = wordFree (w.toList.map some) := by
  unfold StrongConv.Stable.A2.fw wordFree
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  rcases l with i | i <;> rfl

lemma tau_wordOp_sLimit {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    tau (wordOp (sLimit d) w) = if StrongConv.Stable.A2.fw w = 1 then 1 else 0 := by
  rw [wordOp_eq_wordEval, fw_eq_wordFree, Perm.tau_wordEval_sLimit]

lemma sum_inner_tensorOp {D d : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (T : L2Free d →L[ℂ] L2Free d) :
    ∑ a : Fin D, ⟪(PiLp.single 2 a (delta 1) : PiLp 2 (fun _ : Fin D => L2Free d)),
      tensorOp A T (PiLp.single 2 a (delta 1))⟫_ℂ = A.trace * tau T := by
  classical
  simp only [inner_tensorOp, PiLp.single_apply]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · simp [tau]
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem trTau_eval_sLimit {D d : ℕ} (P : NCPoly D d) :
    trTau (P.eval (sLimit d)) =
      (D : ℂ)⁻¹ * ∑ w ∈ P.support, (P w).trace * (if fw w = 1 then 1 else 0) := by
  unfold trTau
  congr 1
  unfold NCPoly.eval
  simp only [FunLike.coe_sum, Finset.sum_apply, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sum_inner_tensorOp, tau_wordOp_sLimit]

end StrongConv.Stable.A2.PartT
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
alias trTau_eval_sLimit := StrongConv.Stable.A2.PartT.trTau_eval_sLimit

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartT
open scoped InnerProductSpace
/-! ### Characters -/
theorem chi_one (π : StableRep) (N : ℕ) : chi π N 1 = π.dim N := by
  simp [StrongConv.Stable.A2.chi]

end StrongConv.Stable.A2.PartT
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
/-! ## Part C: characters -/
alias chi_one := StrongConv.Stable.A2.PartT.chi_one

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartT
open scoped InnerProductSpace

end StrongConv.Stable.A2.PartT
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartD
open StrongConv StrongConv.Stable.A2
open scoped ComplexOrder
/-! ## Uniform probability helpers -/
lemma uniformProb_nonneg {X : Type*} [Fintype X] (E : X → Prop) : 0 ≤ uniformProb E := by
  unfold uniformProb; positivity

lemma uniformProb_mono {X : Type*} [Fintype X] {E F : X → Prop} (h : ∀ x, E x → F x) :
    uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

lemma uniformProb_exists_le {X ι : Type*} [Fintype X] (S : Finset ι) (E : ι → X → Prop) :
    uniformProb (fun x => ∃ i ∈ S, E i x) ≤ ∑ i ∈ S, uniformProb (E i) := by
  classical
  unfold uniformProb
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (Finset.univ.filter fun x => ∃ i ∈ S, E i x) =
      S.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext x; simp
  have h2 := Finset.card_biUnion_le (s := S) (t := fun i => Finset.univ.filter (E i))
  rw [← this] at h2
  have h3 : ((Finset.univ.filter fun x => ∃ i ∈ S, E i x).card : ℝ) ≤
      ∑ i ∈ S, ((Finset.univ.filter (E i)).card : ℝ) := by exact_mod_cast h2
  refine le_of_le_of_eq (le_of_eq_of_le ?_ h3) ?_
  · congr 2; ext x; simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2

/-- Markov's inequality for the uniform distribution. -/
lemma uniformProb_le_markov {X : Type*} [Fintype X] (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    {K : ℝ} (hK : 0 < K) :
    uniformProb (fun x => K ≤ f x) ≤ uniformExp f / K := by
  classical
  unfold uniformProb uniformExp
  rw [div_div, mul_comm, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [le_div_iff₀ hK]
  have key : ((Finset.univ.filter fun x => K ≤ f x).card : ℝ) * K ≤ ∑ x, f x := by
    calc ((Finset.univ.filter fun x => K ≤ f x).card : ℝ) * K
        = ∑ x ∈ Finset.univ.filter (fun x => K ≤ f x), K := by simp
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => K ≤ f x), f x :=
          Finset.sum_le_sum (fun x hx => (Finset.mem_filter.1 hx).2)
      _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x _ _ => hf x)
  convert key using 4

/-! ## Part (1): the dimension tends to infinity -/
lemma mv_eval_const (r : ℕ) (φ : MvPolynomial (Fin r) ℂ) (a : ℂ) :
    MvPolynomial.eval (fun _ : Fin r => a) φ =
      (MvPolynomial.aeval (fun _ : Fin r => (X : ℂ[X])) φ).eval a := by
  induction φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma trace_eq_q (π : StableRep) {N : ℕ} (hN : π.N₀ ≤ N) (σ : Equiv.Perm (Fin N)) (a : ℕ)
    (h : ∀ i : Fin π.r, xi ((i : ℕ) + 1) σ = a) :
    (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace =
      (MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ).eval (a : ℂ) := by
  rw [π.trace_eq N hN σ, ← mv_eval_const]
  simp only [h]

lemma cycle_pow_apply_ne {N : ℕ} {c : Equiv.Perm (Fin N)} (hc : c.IsCycle) {k : ℕ}
    (hk0 : 0 < k) (hk : k < c.support.card) {x : Fin N} (hx : x ∈ c.support) :
    (c ^ k) x ≠ x := by
  intro h
  have h1 : c ^ k = 1 := (hc.pow_eq_one_iff' (Equiv.Perm.mem_support.1 hx)).2 h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hc.orderOf] at h2
  exact absurd (Nat.le_of_dvd hk0 h2) (not_le.2 hk)

lemma xi_cycle {N : ℕ} {c : Equiv.Perm (Fin N)} (hc : c.IsCycle) {k : ℕ}
    (hk0 : 0 < k) (hk : k < c.support.card) :
    xi k c = N - c.support.card := by
  unfold xi
  have : (Finset.univ.filter fun x => (c ^ k) x = x) = Finset.univ \ c.support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h hx; exact cycle_pow_apply_ne hc hk0 hk hx h
    · intro hx
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (Equiv.Perm.notMem_support.1 hx) k
  rw [this, Finset.card_univ_sdiff, Fintype.card_fin]

open Matrix in
lemma unitary_eq_one_of_trace {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (h : (U : Matrix (Fin n) (Fin n) ℂ).trace = n) : (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hU : star (U : Matrix (Fin n) (Fin n) ℂ) * U = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  have key : ((U - 1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U - 1)).trace = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, mul_sub,
      one_mul, mul_one, ← Matrix.star_eq_conjTranspose, hU, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, h]
    simp
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at key
  exact sub_eq_zero.1 key

theorem tendsto_dim_atTop (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) :
    Tendsto (fun N => (π.dim N : ℝ)) atTop atTop := by
  set q := MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ with hq
  have htr1 : ∀ N, ((π.π N 1 : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ)).trace = π.dim N := by
    intro N; simp
  have hdimq : ∀ N, π.N₀ ≤ N → ((π.dim N : ℂ)) = q.eval (N : ℂ) := by
    intro N hN
    rw [← htr1 N]
    refine trace_eq_q π hN 1 N (fun i => ?_)
    simp [xi]
  by_cases hdeg : 0 < q.degree
  · have hz : Tendsto (fun N : ℕ => ‖(N : ℂ)‖) atTop atTop := by
      simpa using tendsto_natCast_atTop_atTop
    have ht := Polynomial.tendsto_norm_atTop q hdeg hz
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop π.N₀] with N hN
    rw [← hdimq N hN]
    simp
  · exfalso
    have hc : q = C (q.coeff 0) := Polynomial.eq_C_of_degree_le_zero (not_lt.1 hdeg)
    set N := π.N₀ + π.r + 3 with hNdef
    have hN : π.N₀ ≤ N := by omega
    have hqN : ∀ a : ℂ, q.eval a = (π.dim N : ℂ) := by
      intro a
      rw [hdimq N hN, hc]; simp
    -- the N-cycle
    set c₁ : Equiv.Perm (Fin N) := finRotate N
    have hc₁ : c₁.IsCycle := isCycle_finRotate_of_le (by omega)
    have hs₁ : c₁.support = Finset.univ := support_finRotate_of_le (by omega)
    have hcard₁ : c₁.support.card = N := by rw [hs₁, Finset.card_univ, Fintype.card_fin]
    set x : Fin N := ⟨0, by omega⟩
    have hx : x ∈ c₁.support := by rw [hs₁]; exact Finset.mem_univ _
    have hcx : c₁ x ≠ x := Equiv.Perm.mem_support.1 hx
    have hccx : c₁ (c₁ x) ≠ x := by
      have := cycle_pow_apply_ne hc₁ (k := 2) (by norm_num) (by omega) hx
      rwa [pow_two, Equiv.Perm.mul_apply] at this
    set c₂ : Equiv.Perm (Fin N) := Equiv.swap x (c₁ x) * c₁
    have hc₂ : c₂.IsCycle := hc₁.swap_mul hcx hccx
    have hs₂ : c₂.support = c₁.support \ {x} := Equiv.Perm.support_swap_mul_eq _ _ hccx
    have hcard₂ : c₂.support.card = N - 1 := by
      rw [hs₂, Finset.card_sdiff_of_subset (by simpa using hx), hcard₁, Finset.card_singleton]
    -- the traces
    have ht₁ : (π.π N c₁ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace = π.dim N := by
      rw [trace_eq_q π hN c₁ 0, hqN]
      intro i
      rw [xi_cycle hc₁ (by omega) (by have := i.2; omega), hcard₁, Nat.sub_self]
    have ht₂ : (π.π N c₂ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace = π.dim N := by
      rw [trace_eq_q π hN c₂ 1, hqN]
      intro i
      rw [xi_cycle hc₂ (by omega) (by have := i.2; omega), hcard₂]
      omega
    have hp₁ : π.π N c₁ = 1 := Subtype.ext (unitary_eq_one_of_trace _ ht₁)
    have hp₂ : π.π N c₂ = 1 := Subtype.ext (unitary_eq_one_of_trace _ ht₂)
    have hsw : π.π N (Equiv.swap x (c₁ x)) = 1 := by
      have : Equiv.swap x (c₁ x) = c₂ * c₁⁻¹ := by simp [c₂]
      rw [this, map_mul, map_inv, hp₁, hp₂]; simp
    have hker : Subgroup.closure ({c₁, Equiv.swap x (c₁ x)} : Set (Equiv.Perm (Fin N))) ≤
        (π.π N).ker := by
      rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact hp₁
      · rw [Set.mem_singleton_iff] at hg; subst hg; exact hsw
    rw [Equiv.Perm.closure_cycle_adjacent_swap hc₁ hs₁ x, top_le_iff] at hker
    have hall : ∀ σ, π.π N σ = 1 := fun σ => by
      have : σ ∈ (π.π N).ker := by rw [hker]; exact Subgroup.mem_top _
      exact this
    have hv := hπ N hN (fun _ => (1 : ℂ)) (fun σ => by rw [hall σ]; simp)
    have := congrFun hv ⟨0, hdim N hN⟩
    simp at this

end StrongConv.Stable.A2.PartD
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartT
open scoped InnerProductSpace
/-! ### Fixed points of a nontrivial word -/
lemma exists_wordFree {d : ℕ} (u : FreeGroup (Fin d)) : ∃ w : List (Letter d), wordFree w = u := by
  induction u using FreeGroup.induction_on with
  | C1 => exact ⟨[], by simp [wordFree]⟩
  | of i => exact ⟨[some (Sum.inl i)], by simp [wordFree]⟩
  | inv_of i _ => exact ⟨[some (Sum.inr i)], by simp [wordFree]⟩
  | mul x y hx hy =>
    obtain ⟨wx, rfl⟩ := hx
    obtain ⟨wy, rfl⟩ := hy
    exact ⟨wx ++ wy, by simp [wordFree]⟩

lemma uniformExp_fixc_eq {d N : ℕ} (hN : 0 < N) (w : List (Letter d)) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        (StrongConv.Stable.A2.fixc (FreeGroup.lift σ (wordFree w)) : ℝ)) =
      1 + N * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [uniformExp, Perm.trN_wordEval_sModel, Perm.wordPerm_eq_lift]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
  simp [Perm.fixCount, StrongConv.Stable.A2.fixc]

lemma gPoly_eval_zero (d q : ℕ) : (gPoly d q).eval 0 = 1 := by
  simp [gPoly, Polynomial.eval_prod]

theorem exists_uniformExp_fixc_le {d : ℕ} (u : FreeGroup (Fin d)) (hu : u ≠ 1) :
    ∃ C : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => (fixc (FreeGroup.lift σ u) : ℝ)) ≤ C := by
  obtain ⟨w, rfl⟩ := exists_wordFree u
  set E : ℕ → ℝ := fun N =>
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w)) with hE
  set q := max 1 w.length with hq
  obtain ⟨-, f, -, hf⟩ :=
    StrongConv.exists_uniformExp_trN_wordEval_eq_div d q (le_max_left _ _) w (le_max_right _ _)
  set g := gPoly d q
  have hg0 : g.eval 0 = 1 := gPoly_eval_zero d q
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- `E N → 0`
  have hlimC := StrongConv.tendsto_uniformExp_trN_wordEval d w
  rw [Perm.tau_wordEval_sLimit, if_neg hu] at hlimC
  have hElim : Tendsto E atTop (𝓝 0) := by
    have := (Complex.continuous_re.tendsto _).comp hlimC
    simpa [Function.comp_def, hE] using this
  -- the rational function tends to `f(0)`
  have hrat : ∀ p : ℝ[X], Tendsto (fun N : ℕ => p.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)))
      atTop (𝓝 (p.eval 0)) := by
    intro p
    have h1 := (p.continuous.tendsto 0).comp hinv
    have h2 := (g.continuous.tendsto 0).comp hinv
    have := h1.div h2 (by rw [hg0]; exact one_ne_zero)
    rw [hg0, div_one] at this
    exact this
  have hf0 : f.eval 0 = 0 := by
    refine tendsto_nhds_unique ?_ hElim
    refine (hrat f).congr' ?_
    filter_upwards [eventually_ge_atTop q] with N hN
    exact (hf N hN).symm
  obtain ⟨f₁, rfl⟩ : X ∣ f := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; exact hf0
  have hNE : ∀ N, q ≤ N → (N : ℝ) * E N = f₁.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)) := by
    intro N hN
    have hN1 : (N : ℝ) ≠ 0 := by
      have : 1 ≤ N := le_trans (le_max_left _ _) hN
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp this)
    change (N : ℝ) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (wordEval (sModel σ) w)) = _
    rw [hf N hN, Polynomial.eval_mul, Polynomial.eval_X]
    field_simp
  have hev := (hrat f₁).eventually (gt_mem_nhds (lt_add_one (f₁.eval 0)))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨1 + (f₁.eval 0 + 1), max N₀ q, fun N hN => ?_⟩
  have hNq : q ≤ N := le_trans (le_max_right _ _) hN
  rw [uniformExp_fixc_eq (lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left 1 _)) hNq)]
  have := hNE N hNq
  have h2 := hN₀ N (le_trans (le_max_left _ _) hN)
  change 1 + (N : ℝ) * E N ≤ _
  rw [this]
  linarith

end StrongConv.Stable.A2.PartT
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
/-! ## Part F: fixed points of a nontrivial word are bounded in mean -/
alias exists_uniformExp_fixc_le := StrongConv.Stable.A2.PartT.exists_uniformExp_fixc_le

end StrongConv.Stable.A2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2.PartD
open StrongConv StrongConv.Stable.A2
open scoped ComplexOrder
/-! ## Part (2): the character of a nontrivial word is small -/
theorem tendsto_prob_norm_chi_ge (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {d : ℕ} (u : FreeGroup (Fin d)) (hu : u ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      δ * (π.dim N : ℝ) ≤ ‖chi π N (FreeGroup.lift σ u)‖)) atTop (𝓝 0) := by
  have hupow : ∀ k : ℕ, k ≠ 0 → u ^ k ≠ 1 := fun k hk h => hu ((pow_eq_one_iff_left hk).1 h)
  have hC : ∀ i : Fin π.r, ∃ C : ℝ, ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        (fixc (FreeGroup.lift σ (u ^ ((i : ℕ) + 1))) : ℝ)) ≤ C :=
    fun i => StrongConv.Stable.A2.exists_uniformExp_fixc_le _ (hupow _ (Nat.succ_ne_zero _))
  choose C N₁ hCN using hC
  have hT := StrongConv.Stable.A2.PartD.tendsto_dim_atTop π hπ hdim
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall (fun N => lt_of_lt_of_le ha (uniformProb_nonneg _)),
    fun ε hε => ?_⟩
  set S : ℝ := ∑ i, |C i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  obtain ⟨K, hK⟩ := exists_nat_gt (S / ε)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ x : Fin π.r → Fin (K + 1),
    ‖MvPolynomial.eval (fun i => ((x i : ℕ) : ℂ)) π.φ‖ := ⟨_, rfl⟩
  have hev := hT.eventually_gt_atTop (B / δ)
  filter_upwards [hev, eventually_ge_atTop π.N₀, eventually_ge_atTop (Finset.univ.sup N₁)]
    with N hB hN0 hN1
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  calc uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        δ * (π.dim N : ℝ) ≤ ‖chi π N (FreeGroup.lift σ u)‖)
      ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) => ∃ i ∈ (Finset.univ : Finset (Fin π.r)),
          ((K : ℝ) + 1) ≤ (fixc (FreeGroup.lift σ (u ^ ((i : ℕ) + 1))) : ℝ)) := by
        apply uniformProb_mono
        intro σ hσ
        by_contra hne
        push Not at hne
        have hx : ∀ i : Fin π.r, xi ((i : ℕ) + 1) (FreeGroup.lift σ u) < K + 1 := by
          intro i
          have h1 := hne i (Finset.mem_univ _)
          have e : xi ((i : ℕ) + 1) (FreeGroup.lift σ u) =
              fixc (FreeGroup.lift σ (u ^ ((i : ℕ) + 1))) := by
            rw [map_pow]; rfl
          rw [e]; exact_mod_cast h1
        have hle : ‖chi π N (FreeGroup.lift σ u)‖ ≤ B := by
          unfold chi
          rw [π.trace_eq N hN0]
          let y : Fin π.r → Fin (K + 1) := fun i => ⟨_, hx i⟩
          have hy : (fun i : Fin π.r => ((xi ((i : ℕ) + 1) (FreeGroup.lift σ u) : ℕ) : ℂ)) =
              fun i => ((y i : ℕ) : ℂ) := rfl
          rw [hy, hBdef]
          exact Finset.single_le_sum
            (f := fun x : Fin π.r → Fin (K + 1) =>
              ‖MvPolynomial.eval (fun i => ((x i : ℕ) : ℂ)) π.φ‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ y)
        have : B < δ * π.dim N := by rwa [div_lt_iff₀' hδ] at hB
        linarith
    _ ≤ ∑ i : Fin π.r, uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((K : ℝ) + 1) ≤ (fixc (FreeGroup.lift σ (u ^ ((i : ℕ) + 1))) : ℝ)) :=
        uniformProb_exists_le _ _
    _ ≤ ∑ i : Fin π.r, |C i| / ((K : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro i _
        refine (uniformProb_le_markov _ (fun _ => Nat.cast_nonneg _) hKpos).trans ?_
        apply div_le_div_of_nonneg_right _ hKpos.le
        exact (hCN i N (le_trans (Finset.le_sup (Finset.mem_univ i)) hN1)).trans
          (le_abs_self _)
    _ = S / ((K : ℝ) + 1) := by rw [Finset.sum_div]
    _ < ε := by
        rw [div_lt_iff₀ hKpos]
        rw [div_lt_iff₀ hε] at hK
        nlinarith

end StrongConv.Stable.A2.PartD
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Stable.A2
open scoped InnerProductSpace
/-! ## Part S: the character of a nontrivial word is small -/
alias tendsto_prob_norm_chi_ge := StrongConv.Stable.A2.PartD.tendsto_prob_norm_chi_ge

lemma uniformProb_nonneg' {X : Type*} [Fintype X] (E : X → Prop) : 0 ≤ uniformProb E := by
  unfold uniformProb; positivity

lemma uniformProb_mono' {X : Type*} [Fintype X] {E F : X → Prop} (h : ∀ x, E x → F x) :
    uniformProb E ≤ uniformProb F := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)

lemma uniformProb_exists_le {X ι : Type*} [Fintype X] (S : Finset ι) (E : ι → X → Prop) :
    uniformProb (fun x => ∃ i ∈ S, E i x) ≤ ∑ i ∈ S, uniformProb (E i) := by
  classical
  unfold uniformProb
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (Finset.univ.filter fun x => ∃ i ∈ S, E i x) =
      S.biUnion (fun i => Finset.univ.filter (E i)) := by
    ext x; simp
  have h2 := Finset.card_biUnion_le (s := S) (t := fun i => Finset.univ.filter (E i))
  rw [← this] at h2
  have h3 : ((Finset.univ.filter fun x => ∃ i ∈ S, E i x).card : ℝ) ≤
      ∑ i ∈ S, ((Finset.univ.filter (E i)).card : ℝ) := by exact_mod_cast h2
  refine le_of_le_of_eq (le_of_eq_of_le ?_ h3) ?_
  · congr 2; ext x; simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2

theorem tendsto_prob_norm_trace_sub_trTau_ge_dev (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {D d : ℕ} (P : NCPoly D d) (_hP : P.IsSelfAdjoint)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      η ≤ ‖LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((P.eval (π.model σ) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) /
          ((D : ℂ) * (π.dim N : ℂ)) - trTau (P.eval (sLimit d))‖))
      atTop (𝓝 0) := by
  classical
  set S := P.support.filter (fun w => fw w ≠ 1) with hS
  set n : ℝ := (S.card : ℝ) with hn
  let a : FreeMonoid (Fin d ⊕ Fin d) → ℝ := fun w => ‖(P w).trace / (D : ℂ)‖ + 1
  have ha : ∀ w, 0 < a w := fun w => by positivity
  let δ : FreeMonoid (Fin d ⊕ Fin d) → ℝ := fun w => η / ((n + 1) * a w)
  have hδ : ∀ w, 0 < δ w := fun w => by positivity
  have hlim : Tendsto (fun N : ℕ => ∑ w ∈ S, uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      δ w * (π.dim N : ℝ) ≤ ‖chi π N (FreeGroup.lift σ (fw w))‖)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ w ∈ S, (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun w hw => ?_
    have hw1 : fw w ≠ 1 := (Finset.mem_filter.mp hw).2
    exact tendsto_prob_norm_chi_ge π hπ hdim (fw w) hw1 (δ w) (hδ w)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun N => uniformProb_nonneg' _) ?_
  filter_upwards [eventually_ge_atTop π.N₀] with N hN
  refine le_trans (uniformProb_mono' fun σ hσ => ?_) (uniformProb_exists_le S _)
  -- the pointwise inclusion
  have hDn : 0 < π.dim N := hdim N hN
  have hDnR : (0 : ℝ) < π.dim N := by exact_mod_cast hDn
  have hDnC : (π.dim N : ℂ) ≠ 0 := by exact_mod_cast hDn.ne'
  rw [trace_eval_model, trTau_eval_sLimit] at hσ
  -- rewrite the difference as a sum over `S`
  have hdiff : (∑ w ∈ P.support, (P w).trace * chi π N (FreeGroup.lift σ (fw w))) /
        ((D : ℂ) * (π.dim N : ℂ)) -
      (D : ℂ)⁻¹ * ∑ w ∈ P.support, (P w).trace * (if fw w = 1 then 1 else 0) =
      ∑ w ∈ S, (P w).trace / (D : ℂ) * (chi π N (FreeGroup.lift σ (fw w)) / (π.dim N : ℂ)) := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h1 : fw w = 1
    · rw [if_pos h1, if_neg (not_not.mpr h1), h1, map_one, chi_one]
      field_simp
      simp
    · rw [if_neg h1, if_pos h1]
      ring
  rw [hdiff] at hσ
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ w ∈ S, ‖(P w).trace / (D : ℂ) * (chi π N (FreeGroup.lift σ (fw w)) /
      (π.dim N : ℂ))‖ < η / (n + 1) := by
    intro w hw
    have h1 := hcon w hw
    rw [norm_mul, norm_div ((chi π N _)), Complex.norm_natCast]
    have hchi := norm_nonneg (chi π N (FreeGroup.lift σ (fw w)))
    have hb : ‖(P w).trace / (D : ℂ)‖ ≤ a w := by simp [a]
    calc ‖(P w).trace / (D : ℂ)‖ * (‖chi π N (FreeGroup.lift σ (fw w))‖ / (π.dim N : ℝ))
        ≤ a w * (‖chi π N (FreeGroup.lift σ (fw w))‖ / (π.dim N : ℝ)) := by gcongr
      _ < a w * (δ w * (π.dim N : ℝ) / (π.dim N : ℝ)) := by
          gcongr
      _ = η / (n + 1) := by
          simp only [δ]
          have := (ha w).ne'
          field_simp
  have hsum : ‖∑ w ∈ S, (P w).trace / (D : ℂ) * (chi π N (FreeGroup.lift σ (fw w)) /
      (π.dim N : ℂ))‖ ≤ n * (η / (n + 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w ∈ S, ‖(P w).trace / (D : ℂ) * (chi π N (FreeGroup.lift σ (fw w)) /
          (π.dim N : ℂ))‖ ≤ ∑ _w ∈ S, η / (n + 1) := Finset.sum_le_sum fun w hw => (hlt w hw).le
      _ = n * (η / (n + 1)) := by simp [hn]
  have hn0 : 0 ≤ n := by positivity
  have : n * (η / (n + 1)) < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

end StrongConv.Stable.A2
end
end

end
end

section
open StrongConv

open Polynomial Filter Topology


theorem solution (π : StableRep) (hπ : π.NoTrivialSummand)
    (hdim : ∀ N, π.N₀ ≤ N → 0 < π.dim N) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
      η ≤ ‖LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((P.eval (π.model σ) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) /
          ((D : ℂ) * (π.dim N : ℂ)) - trTau (P.eval (sLimit d))‖))
      atTop (𝓝 0) := by
  apply StrongConv.Stable.A2.tendsto_prob_norm_trace_sub_trTau_ge_dev <;> assumption

end
