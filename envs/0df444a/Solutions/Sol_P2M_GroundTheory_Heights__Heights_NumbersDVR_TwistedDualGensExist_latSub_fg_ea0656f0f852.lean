-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_latSub_fg_ea0656f0f852
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:25:26.967801+00:00
-- url     : https://prove2.me/submissions/24b2ac69-06ff-4836-ace4-552f21226787

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86

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
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution {x : τ → Ω} (B : ChartBundle O x r E) {c : τ} (hc : x c ≠ 0) :
    (TwistedDualGensExist.latSub B c).FG := by
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  have hbl : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat c := fun l q =>
    (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by by_cases h : q' = q <;> simp [h]⟩,
      by simp [Pi.single_apply]⟩
  choose n hn using hbl
  refine ⟨(Set.finite_range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  set P := Submodule.span (chartRing O x c)
    (Set.range fun p : Fin k × Fin r => f p.1 ^ n p.1 p.2 • b p.1 p.2) with hP
  have hsm : ∀ {a : Ω}, a ∈ chartRing O x c → ∀ {v : E}, v ∈ P → a • v ∈ P :=
    fun {a} ha {v} hv => P.smul_mem (⟨a, ha⟩ : chartRing O x c) hv
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hn p.1 p.2
  · intro e he
    have he' : e ∈ B.lat c := he
    have hloc : ∀ l, ∃ M : ℕ, ∀ M', M ≤ M' → f l ^ M' • e ∈ P := by
      intro l
      obtain ⟨a, ha, hea⟩ := (hiff l e).1 ⟨0, by simpa using he'⟩
      choose m hm using ha
      refine ⟨∑ q, (m q + n l q), fun M' hM' => ?_⟩
      rw [hea, Finset.smul_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      have hq : m q + n l q ≤ M' :=
        le_trans (Finset.single_le_sum (f := fun q => m q + n l q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)) hM'
      have heq : f l ^ M' • a q • b l q =
          (f l ^ (M' - (m q + n l q)) * (f l ^ m q * a q)) • (f l ^ n l q • b l q) := by
        rw [smul_smul, smul_smul]
        congr 1
        rw [← Nat.sub_add_cancel hq]
        simp only [Nat.add_sub_cancel, pow_add]
        ring
      rw [heq]
      exact hsm (mul_mem (pow_mem (hf l) _) (hm q)) (Submodule.subset_span ⟨(l, q), rfl⟩)
    choose Ml hMl using hloc
    obtain ⟨g, hg, hgsum⟩ := TwistedDualGensExist.exists_pow_combination (chartRing O x c) f cc hf hcc
      hsum (∑ l, Ml l)
    have : e = ∑ l, g l • (f l ^ (∑ l, Ml l) • e) := by
      simp only [smul_smul, ← Finset.sum_smul, hgsum, one_smul]
    show e ∈ P
    rw [this]
    refine Submodule.sum_mem _ fun l _ => hsm (hg l) (hMl l _ ?_)
    exact Finset.single_le_sum (f := Ml) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
