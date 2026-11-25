-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyc_re_psum_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:08.750942+00:00
-- url     : https://prove2.me/submissions/26a7eef0-fe94-461c-8163-6e33bcf71e61

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne

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
theorem _root_.solution (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → (Psum E χ s).re ≤ C := by
  by_cases hχ : χ = 1
  · exact ⟨0, Eventually.of_forall fun _ h => absurd hχ h⟩
  obtain ⟨L1, hL⟩ := hK E l hirr χ hχ
  obtain ⟨C3, hC3⟩ := h3a E l χ
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Lser E χ s‖ < ‖L1‖ + 1 :=
    ((continuous_norm.tendsto L1).comp hL).eventually (gt_mem_nhds (by linarith))
  refine ⟨Real.log (‖L1‖ + 1) + C3, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with s hs (hs1 : 1 < s) _
  have he : Complex.exp (abelian₂ E χ s) = Lser E χ s := h2 E l χ s hs1
  have hre : Real.exp (abelian₂ E χ s).re < ‖L1‖ + 1 := by rw [← Complex.norm_exp, he]; exact hs
  have hlam : (abelian₂ E χ s).re < Real.log (‖L1‖ + 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]; exact hre
  have hd : |(abelian₂ E χ s - Psum E χ s).re| ≤ C3 := (Complex.abs_re_le_norm _).trans (hC3 s hs1)
  rw [Complex.sub_re] at hd
  linarith [(abs_le.mp hd).1]
end ReciprocityTheory.Cheb
