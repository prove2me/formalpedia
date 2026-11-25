-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Uz_le_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:38.485084+00:00
-- url     : https://prove2.me/submissions/20c9671a-d22f-484e-be4a-9416e5437d34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_Iperp_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_ucomp_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) {z : Frame X.Ψ r} {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz z ξ) :
    u ∈ Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) := by
  let Q : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) :=
    { toFun := fun v => X.ucomp z ξ v
      map_add' := fun v v' => by
        funext τ
        show (v τ + v' τ) - (X.Hf z τ (v τ + v' τ) (Data.emb τ.1 ξ) /
          X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ = _
        rw [UnipotentCoefficientShift.Hf_add_left, add_div, add_smul]
        show _ = (v τ - _) + (v' τ - _)
        abel
      map_smul' := fun a v => by
        funext τ
        show a • v τ - (X.Hf z τ (a • v τ) (Data.emb τ.1 ξ) /
          X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
            a • (v τ - (X.Hf z τ (v τ) (Data.emb τ.1 ξ) /
              X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ)
        rw [← Complex.coe_smul a (v τ), UnipotentCoefficientShift.Hf_smul_left, ← Complex.coe_smul a, mul_div_assoc]
        module }
  have h1 := Iperp_le hD3 hξ hu.1
  have h2 : Submodule.map Q (Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) ≤
      Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨⟨μ, hμ⟩, rfl⟩
  have h3 := h2 (Submodule.mem_map_of_mem h1)
  have e : Q u = u := MajorantOperators.ucomp_of_mem hu
  rwa [e] at h3
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
