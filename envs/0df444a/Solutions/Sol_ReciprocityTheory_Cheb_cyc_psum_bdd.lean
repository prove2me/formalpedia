-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyc_psum_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:17.136944+00:00
-- url     : https://prove2.me/submissions/c91baa69-65fd-4a10-a8ea-c76f3f13cc9a

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne
import Theorems.Thm_ReciprocityTheory_Cheb_cyc_re_psum_lower
import Theorems.Thm_ReciprocityTheory_Cheb_bdd_of_exp_tendsto


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Psum E χ s‖ ≤ B := by
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C, hC⟩ := cyc_re_psum_lower (E := E) h1 h2 h3a hK hS1 hirr χ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hlow : ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.exp (-(C + C3)) ≤ ‖Lser E χ s‖ := by
    filter_upwards [hC, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
    rw [← h2 E l χ s hgt, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hgt)
    rw [Complex.sub_re] at hd
    linarith [(abs_le.mp hd).1]
  have hL0 : L1 ≠ 0 := by
    have := ge_of_tendsto ((continuous_norm.tendsto L1).comp hL) hlow
    intro h0
    rw [h0, norm_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))
  have hexp : Tendsto (fun s => Complex.exp (abelian₂ E χ s)) (𝓝[>] 1) (𝓝 L1) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    exact (h2 E l χ s hs).symm
  obtain ⟨B, hB⟩ := bdd_of_exp_tendsto _ (h3c E l χ) L1 hL0 hexp
  refine ⟨B + C3, ?_⟩
  filter_upwards [hB, self_mem_nhdsWithin] with s hs (hgt : 1 < s)
  have := hC3 s hgt
  calc ‖Psum E χ s‖ = ‖abelian₂ E χ s - (abelian₂ E χ s - Psum E χ s)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖abelian₂ E χ s‖ + ‖abelian₂ E χ s - Psum E χ s‖ := norm_sub_le _ _
    _ ≤ B + C3 := by linarith
end ReciprocityTheory.Cheb
