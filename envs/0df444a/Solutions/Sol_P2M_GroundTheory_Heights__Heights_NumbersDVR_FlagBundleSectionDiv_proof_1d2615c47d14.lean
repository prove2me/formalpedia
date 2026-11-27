-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDiv_proof_1d2615c47d14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:31.458349+00:00
-- url     : https://prove2.me/submissions/1bfba0bd-0376-4063-b8d7-8568ffb4c7b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_eq_zero_of_not_mem_cb50906fea03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_divCycle_congr_3f7c8e7470ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open FlagBundleSectionDivProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagBundleSectionDiv
theorem _root_.solution (hDim : FlagBundleDim.Statement)
    (hSat : MultAtOfSaturated.Statement.{0}) (hForm : ProjIdealFormValue.Statement)
    (hTrunc : TruncSpecialize.Statement) (hChart : FlagBundleChartSection.Statement) :
    FlagBundleSectionDiv.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi bf bg f g hf hg
    hdeg hgP hval W
  classical
  have hQ : IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi i.2.le).1
  have hP : IsMultiProjPrime (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2).1
  have := hP.isPrime
  have := hQ.isPrime
  obtain ⟨hPQ, hspec⟩ := hTrunc F Ω K ι y N E w M φ Φ t ht i
  have hti : t i ≠ 0 := ht.ne_zero i
  have hval0 := fun (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F) (hx : IsMultiHomog x d) =>
    hForm F Ω K ι y N E w M φ Φ (truncCoord t ((i : ℕ) + 1)) d x hx
  have hgv := fun h => hgP ((hval0 _ _ hg).mpr h)
  have hfP : f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
    mul_ne_zero hti hgv (hval ▸ (hval0 _ _ hf).mp h)
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hW
    choose c hc using fun k => hWrel (some k)
    have hy : segreVec y c ≠ 0 := by
      unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro k _ hk
      apply hc k (hPW ?_)
      rw [hval0 _ _ (isWeightedHomogeneous_X F _ _), eval₂_X]
      simp [projCoord, hk]
    obtain ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩ :=
      hChart F Ω K ι y N E B w b hB M a φ hφ Φ t ht i c hy
    have hsW : ∀ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n ∉ W := by
      intro n h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp (hWp.mem_of_pow_mem n h)
      exact hc k hk
    have hμW : μ ∉ W := by
      rw [hμ]
      intro h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp h
      exact hc k (hWp.mem_of_pow_mem _ hk)
    have hμP : μ ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h => hμW (hPW h)
    have hμv := fun h => hμP ((hval0 _ _ hμh).mpr h)
    have hlP : l ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
      mul_ne_zero hti hμv (hlv ▸ (hval0 _ _ hl).mp h)
    have hdeg' : bf + dm = dl + bg := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : f * μ - l * g ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      have h2 := hl.mul hg
      rw [← hdeg'] at h2
      have h1 : IsMultiHomog (f * μ - l * g) (bf + dm) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hf.mul hμh))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
      rw [hval0 _ _ h1, eval₂_sub, eval₂_mul, eval₂_mul, hval, hlv]
      ring
    have hrat : ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
        divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) l W := by
      have h1 := congrFun (divCycle_congr hdiff) W
      rw [DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ f μ hP.isPrime hfP hμP,
        DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ l g hP.isPrime hlP hgP] at h1
      simp only [Pi.add_apply, divCycle_eq_zero_of_not_mem hμW] at h1
      unfold ratDiv
      omega
    rw [hrat]
    have hlQ : l ∈ projIdeal F y w φ (truncCoord t i) :=
      (hForm F Ω K ι y N E w M φ Φ (truncCoord t i) dl l hl).mpr (hspec l μ hlv)
    split_ifs with hWQ
    · subst hWQ
      obtain ⟨hmin, hmult⟩ := hSat F (Option K) (bundleIdx ι M) _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hlQ))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat q hq
          exact ⟨_, hsW n, hn⟩)
      unfold divCycle
      rw [dif_pos ⟨hmin, hQ.relevant⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h
        · exact h.1
        · exact absurd rfl hne
      have hQW : projIdeal F y w φ (truncCoord t i) ≤ W := fun q hq => by
        obtain ⟨n, hn⟩ := hsat q hq
        exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (hsW n)
      have hPQ' : projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) < projIdeal F y w φ (truncCoord t i) :=
        lt_of_le_of_ne hPQ (fun h => hlP (by rw [h]; exact hlQ))
      exact hWQ (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm
  · have h0 : ∀ x, divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) x W = 0 := fun x => by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h, hr⟩
      exact hW ⟨h.1.1, hr, le_sup_left.trans h.1.2⟩
    have hWQ : W ≠ projIdeal F y w φ (truncCoord t i) := by
      rintro rfl
      exact hW ⟨hQ.isPrime, hQ.relevant, hPQ⟩
    simp [ratDiv, h0, hWQ]
end FlagBundleSectionDiv
end GroundTheory.Heights₂.Heights.NumbersDVR
