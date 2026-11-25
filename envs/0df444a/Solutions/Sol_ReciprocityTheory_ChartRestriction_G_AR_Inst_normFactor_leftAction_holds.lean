-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_leftAction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:30.394618+00:00
-- url     : https://prove2.me/submissions/1430d1e2-3e51-4217-9c45-c4fb38de877b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst
open NumberField ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem ringHom_cc_eq_conj (τ : E →+* ℂ) (y : E) : τ (cc y) = starRingEnd ℂ (τ y) :=
  NumberField.IsCMField.complexEmbedding_complexConj E τ y
private theorem sum_mul_gram_mul_cc_of_isUStab {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ) (j l : Fin r) :
    ∑ a, ∑ b, (γ : Matrix (Fin r) (Fin r) E) a j * G a b * cc ((γ : Matrix (Fin r) (Fin r) E) b l)
      = G j l := by
  have hs : ∀ k : Fin r, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (Pi.single k 1)
      = fun a => (γ : Matrix (Fin r) (Fin r) E) a k := by
    intro k
    funext a
    change ∑ c, (γ : Matrix (Fin r) (Fin r) E) a c * (Pi.single k (1 : E) : Fin r → E) c = _
    simp [Pi.single_apply]
  have h := hγ.1 (Pi.single j 1) (Pi.single l 1)
  rw [hs j, hs l] at h
  have hc : ∀ c : Fin r, cc ((Pi.single l (1 : E) : Fin r → E) c) = (Pi.single l (1 : E) : Fin r → E) c := by
    intro c
    by_cases hcl : c = l
    · subst hcl
      simp [cc]
    · simp [cc, hcl]
  change herm G (fun a => (γ : Matrix (Fin r) (Fin r) E) a j)
    (fun a => (γ : Matrix (Fin r) (Fin r) E) a l) = G j l
  rw [h]
  simp only [herm, hc]
  simp [Pi.single_apply]
private theorem sum_four_comm_arakelov_instances {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℂ) :
    ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := by
  calc ∑ a, ∑ b, ∑ j, ∑ l, F a b j l = ∑ a, ∑ j, ∑ b, ∑ l, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ l, ∑ b, F a b j l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ l, ∑ b, F a b j l := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ a, ∑ b, F a b j l := Finset.sum_congr rfl fun j _ => Finset.sum_comm
private theorem hermC_mulVec_map_of_isUStab {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (u v : Fin r → ℂ) :
    hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v) = hermC τ G u v := by
  have key : ∀ j l : Fin r, ∑ a, ∑ b, τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l)) = τ (G j l) := by
    intro j l
    rw [← sum_mul_gram_mul_cc_of_isUStab G Λ γ hγ j l]
    simp only [map_sum, map_mul, ringHom_cc_eq_conj]
  have hmv : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (i : Fin r),
      Matrix.mulVec M w i = ∑ j, M i j * w j := fun _ _ _ => rfl
  have lhs : hermC τ G (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) u)
        (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) v)
      = ∑ a, ∑ b, ∑ j, ∑ l, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
          starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by
    simp only [hermC, hmv, Matrix.map_apply, map_sum, map_mul]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have rhs : hermC τ G u v = ∑ j, ∑ l, ∑ a, ∑ b, u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) *
      τ (G a b) * starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l) := by
    simp only [hermC]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← key j l]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [lhs, rhs]
  exact sum_four_comm_arakelov_instances (fun a b j l => u j * (τ ((γ : Matrix (Fin r) (Fin r) E) a j) * τ (G a b) *
      starRingEnd ℂ (τ ((γ : Matrix (Fin r) (Fin r) E) b l))) * starRingEnd ℂ (v l))
private theorem gram_map_mul_of_isUStab' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E) (hγ : IsUStab G Λ γ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hcol : ∀ a, col ((γ : Matrix (Fin r) (Fin r) E).map τ * M) a
      = Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ) (col M a) := fun _ => rfl
  ext a b
  simp only [gram, Matrix.of_apply, hcol, hermC_mulVec_map_of_isUStab τ G Λ γ hγ]
private theorem dmin_lact_of_mem_Γ {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  simp only [dmin, hm, gram_map_mul_of_isUStab' τ.1 X.Gm X.Λ γ (X.Γ_stab γ hγ)]
end
end ReciprocityTheory.ChartRestriction.G.AR.Inst
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst
open NumberField ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst
theorem _root_.solution : NfacLactStatement (E := E) := by
  unfold NfacLactStatement
  intro r X la γ hγ x hx
  simp only [Data.nfac, dmin_lact_of_mem_Γ X γ hγ]
end ReciprocityTheory.ChartRestriction.G.AR.Inst
