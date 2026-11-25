-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:19:00.521849+00:00
-- url     : https://prove2.me/submissions/abc44950-16ab-457b-b374-a2a7e9331696

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne
import Theorems.Thm_ReciprocityTheory_Cheb_cyc_pcl_large
import Theorems.Thm_ReciprocityTheory_Cheb_finite_norm_mem
import Theorems.Thm_ReciprocityTheory_Cheb_summable_nonprime_norm
import Theorems.Thm_ReciprocityTheory_Cheb_two_le_nrm__ac429c


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
theorem _root_.solution (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3b : faceMap_castSucc_comp_eq_succ) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1) :
    CycStatement := by
  intro E _ _ l _ hirr a T
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hbad : ∀ q : Prm E, (Nrm q).Prime → Nrm q ∉ T → ((Nrm q : ℕ) : ZMod l) ≠ a :=
    fun q hp hT => hno q.asIdeal q.isPrime hp hT
  let g : Prm E → ℝ := fun q => (if (Nrm q).Prime then (0 : ℝ) else ((Nrm q : ℕ) : ℝ)⁻¹) +
    Set.indicator {q | Nrm q ∈ T} (fun _ => (1 : ℝ)) q
  have hg : Summable g :=
    summable_nonprime_norm.add (summable_of_hasFiniteSupport ((finite_norm_mem T).subset Set.support_indicator_subset))
  have hle : ∀ s : ℝ, 1 < s → Pcl E l (a : ZMod l) s ≤ ∑' q, g q := by
    intro s hs
    have hS := h1.2.2 E s hs
    have hterm : ∀ q : Prm E, (if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) ≤ g q := by
      intro q
      have h2q := two_le_nrm q
      have hN1 : (1 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Nrm q)
      have hpow1 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have hpow2 : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
      have hind0 : 0 ≤ Set.indicator {q : Prm E | Nrm q ∈ T} (fun _ => (1 : ℝ)) q :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) q
      have hinv0 : 0 ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by positivity
      simp only [g]
      by_cases hc : ((Nrm q : ℕ) : ZMod l) = a
      · rw [if_pos hc]
        by_cases hp : (Nrm q).Prime
        · have hT : Nrm q ∈ T := by
            by_contra hT; exact hbad q hp hT hc
          rw [if_pos hp, Set.indicator_of_mem (show q ∈ {q : Prm E | Nrm q ∈ T} from hT)]
          linarith
        · rw [if_neg hp]; linarith
      · rw [if_neg hc]
        split_ifs <;> linarith
    have hP : Summable (fun q : Prm E =>
        if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
      refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hS
      · split_ifs
        · positivity
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · positivity
    exact Summable.tsum_le_tsum hterm hP hg
  obtain ⟨s, hs, hs1⟩ := ((cyc_pcl_large (E := E) h1 h2 h3a h3b h3c hK hS1 hirr a (∑' q, g q + 1)).and
    self_mem_nhdsWithin).exists
  linarith [hle s hs1]
end ReciprocityTheory.Cheb
