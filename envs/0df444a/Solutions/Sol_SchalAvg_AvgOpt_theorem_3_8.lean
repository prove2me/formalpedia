-- Prove2me | solution 1 for SchalAvg.AvgOpt.theorem_3_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:52:39.373963+00:00
-- url     : https://prove2.me/submissions/2fb41be5-20d5-426c-a7fc-4a70e5609fc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Theorems.Thm_SchalAvg_AvgOpt_lemma_1_2
import Theorems.Thm_SchalAvg_AvgOpt_prop_1_3
import Theorems.Thm_SchalAvg_AvgOpt_prop_2_1
import Theorems.Thm_SchalAvg_AvgOpt_prop_3_5
import Theorems.Thm_SchalAvg_AvgOpt_prop_3_5_S

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter FeinbergLiang.ACOE

namespace SchalAvg.AvgOpt.T38

open SchalAvg.AvgOpt

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

lemma admissible_stat [MeasurableSingletonClass A] (M : Model S A) {f : S → A}
    (hf : IsStationary M f) : Admissible M (statPolicy hf) := by
  intro t h
  simp only [statPolicy, Policy.ofStationary, Kernel.deterministic_apply]
  rw [Measure.dirac_apply]
  simp [hf.2 h.2]

lemma exists_seq_gLower (M : Model S A) :
    ∃ β : ℕ → ℝ, (∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto β atTop (𝓝 1) ∧
      Tendsto (fun k => ENNReal.ofReal (1 - β k) * mβ M (β k)) atTop (𝓝 (gLower M)) := by
  obtain ⟨x, hx1, hx2⟩ := exists_seq_tendsto_liminf (f := 𝓝[<] (1 : ℝ))
    (u := fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β)
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hx2.eventually hmem)
  refine ⟨fun k => x (k + N), fun k => hN _ (by omega), ?_, ?_⟩
  · exact (tendsto_nhdsWithin_iff.1 hx2).1.comp (tendsto_add_atTop_nat N)
  · exact hx1.comp (tendsto_add_atTop_nat N)

lemma wLow_lsc [TopologicalSpace S] (M : Model S A) (β : ℕ → ℝ) :
    LowerSemicontinuous (wLow M β) := by
  intro x y hy
  obtain ⟨z, hyz, hz⟩ : ∃ z, y < z ∧ ∀ᶠ p in atTop ×ˢ 𝓝 x, z ≤ wβ M (β p.1) p.2 := by
    obtain ⟨z, hz1, hz2⟩ := exists_between hy
    refine ⟨z, hz1, ?_⟩
    have := Filter.eventually_lt_of_lt_liminf hz2
    exact this.mono fun p hp => hp.le
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.1 hz
  obtain ⟨U, hUt, hUo, hxU⟩ := mem_nhds_iff.1 ht₂
  filter_upwards [hUo.mem_nhds hxU] with x' hx'
  refine lt_of_lt_of_le hyz ?_
  apply Filter.le_liminf_of_le
  · isBoundedDefault
  · exact Filter.mem_of_superset (Filter.prod_mem_prod ht₁ (Filter.mem_of_superset
      (hUo.mem_nhds hx') hUt)) hsub

lemma wLow_ne_top [TopologicalSpace S] (M : Model S A) (hB : CondB M) (β : ℕ → ℝ)
    (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (x : S) : wLow M β x ≠ ⊤ := by
  apply ne_top_of_le_ne_top (hB x).ne
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.1 hU
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 ht₁
  refine ⟨(N, x), hsub ⟨hN N le_rfl, mem_of_mem_nhds ht₂⟩, ?_⟩
  exact le_biSup (fun b => wβ M b x) (hβ N)

lemma wLowDisc_ne_top (M : Model S A) (hB : CondB M) (β : ℕ → ℝ)
    (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (x : S) : wLowDisc M β x ≠ ⊤ := by
  apply ne_top_of_le_ne_top (hB x).ne
  apply Filter.liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall fun k => le_biSup (fun b => wβ M b x) (hβ k)

lemma tendsto_seq_of_tendsto (M : Model S A)
    (htend : Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1) (𝓝 (gLower M)))
    (β : ℕ → ℝ) (hβ : ∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1)) :
    Tendsto (fun k => ENNReal.ofReal (1 - β k) * mβ M (β k)) atTop (𝓝 (gLower M)) := by
  have : Tendsto β atTop (𝓝[<] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hβ1, Eventually.of_forall fun k => (hβ k).2⟩
  exact htend.comp this

lemma tendsto_m (M : Model S A) (h : gLower M = gUpper M) :
    Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1) (𝓝 (gLower M)) :=
  tendsto_of_liminf_eq_limsup rfl h.symm

end SchalAvg.AvgOpt.T38

open SchalAvg.AvgOpt SchalAvg.AvgOpt.T38

theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [TopologicalSpace S]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model S A) (hGA : GeneralAssumption M) (hB : CondB M) :
    -- Condition (W): an average-optimal f₁, and limit discount optimality in the sense of 3.5(ii)
    (CondW M →
      (∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁, ∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
      ∀ β : ℕ → ℝ, (∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) → Tendsto β atTop (𝓝 1) →
      ∀ fβ : ℕ → S → A, (∀ k, IsDiscOptimal M (β k) (fβ k)) →
        ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
          (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
          ∀ x, ∃ (km : ℕ → ℕ) (xm : ℕ → S), Tendsto km atTop atTop ∧
            Tendsto xm atTop (𝓝 x) ∧ Tendsto (fun m => fβ (km m) (xm m)) atTop (𝓝 (f₁ x))) ∧
    -- Condition (S): an average-optimal f₁, and limit discount optimality in the sense of (3.7)
    (CondS M →
      (∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁, ∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
      ∀ β : ℕ → ℝ, (∀ k, β k ∈ Set.Ioo (0 : ℝ) 1) → Tendsto β atTop (𝓝 1) →
      ∀ fβ : ℕ → S → A, (∀ k, IsDiscOptimal M (β k) (fβ k)) →
        ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
          (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧
          ∀ x, ∃ km : ℕ → ℕ, Tendsto km atTop atTop ∧
            Tendsto (fun m => fβ (km m) x) atTop (𝓝 (f₁ x))) ∧
    -- g = lim_{β → 1} (1 − β) m_β = lim_{β → 1} (1 − β) v_β
    (CondW M ∨ CondS M →
      Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * mβ M β) (𝓝[<] 1) (𝓝 (gStar M)) ∧
      ∀ x, Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * vβ M β x) (𝓝[<] 1)
        (𝓝 (gStar M))) := by
  -- Step 1 (W): an average-optimal stationary policy, and `g = g̲ = ḡ`.
  have hWex : CondW M → ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
      (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧ gStar M = gLower M ∧
        gLower M = gUpper M := by
    intro hW
    have hBor : BorelSpace S := hW.1.1
    have hLC : LocallyCompactSpace S := hW.1.2.1
    have hSC : SecondCountableTopology S := hW.1.2.2.1
    have hT2 : T2Space S := hW.1.2.2.2
    obtain ⟨β, hβ, hβ1, h31⟩ := exists_seq_gLower M
    have hfβ : ∀ k, ∃ f, IsDiscOptimal M (β k) f :=
      fun k => (prop_2_1 M (β k) (hβ k)).1 (Or.inl hW)
    choose fβ hfβ using hfβ
    have hmeas : Measurable (wLow M β) := (wLow_lsc M β).measurable
    have hfin := wLow_ne_top M hB β hβ
    letI : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
    obtain ⟨f₁, hf₁, hACOI, -⟩ := prop_3_5 M hGA hW hB β hβ hβ1 h31 fβ hfβ
    exact ⟨f₁, hf₁, prop_1_3 M hGA (wLow M β) hmeas hfin f₁ hf₁ hACOI⟩
  -- Step 1 (S).
  have hSex : CondS M → ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
      (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧ gStar M = gLower M ∧
        gLower M = gUpper M := by
    intro hS
    obtain ⟨β, hβ, hβ1, h31⟩ := exists_seq_gLower M
    have hfβ : ∀ k, ∃ f, IsDiscOptimal M (β k) f :=
      fun k => (prop_2_1 M (β k) (hβ k)).1 (Or.inr hS)
    choose fβ hfβ using hfβ
    have hmeas : Measurable (wLowDisc M β) := by
      apply Measurable.liminf
      intro k
      exact ((prop_2_1 M (β k) (hβ k)).2.2.2 hS).sub measurable_const
    have hfin := wLowDisc_ne_top M hB β hβ
    obtain ⟨f₁, hf₁, hACOI, -⟩ := prop_3_5_S M hGA hS hB β hβ hβ1 h31 fβ hfβ
    exact ⟨f₁, hf₁, prop_1_3 M hGA (wLowDisc M β) hmeas hfin f₁ hf₁ hACOI⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hW
    obtain ⟨f₀, hf₀, hPhi₀, hgl, hlu⟩ := hWex hW
    refine ⟨⟨f₀, hf₀, hPhi₀⟩, ?_⟩
    intro β hβ hβ1 fβ hfβ
    have hBor : BorelSpace S := hW.1.1
    have hLC : LocallyCompactSpace S := hW.1.2.1
    have hSC : SecondCountableTopology S := hW.1.2.2.1
    have hT2 : T2Space S := hW.1.2.2.2
    have h31 := tendsto_seq_of_tendsto M (tendsto_m M hlu) β hβ hβ1
    have hmeas : Measurable (wLow M β) := (wLow_lsc M β).measurable
    have hfin := wLow_ne_top M hB β hβ
    letI : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
    obtain ⟨f₁, hf₁, hACOI, hlim⟩ := prop_3_5 M hGA hW hB β hβ hβ1 h31 fβ hfβ
    exact ⟨f₁, hf₁, (prop_1_3 M hGA (wLow M β) hmeas hfin f₁ hf₁ hACOI).1, hlim⟩
  · intro hS
    obtain ⟨f₀, hf₀, hPhi₀, hgl, hlu⟩ := hSex hS
    refine ⟨⟨f₀, hf₀, hPhi₀⟩, ?_⟩
    intro β hβ hβ1 fβ hfβ
    have h31 := tendsto_seq_of_tendsto M (tendsto_m M hlu) β hβ hβ1
    have hmeas : Measurable (wLowDisc M β) := by
      apply Measurable.liminf
      intro k
      exact ((prop_2_1 M (β k) (hβ k)).2.2.2 hS).sub measurable_const
    have hfin := wLowDisc_ne_top M hB β hβ
    obtain ⟨f₁, hf₁, hACOI, hlim⟩ := prop_3_5_S M hGA hS hB β hβ hβ1 h31 fβ hfβ
    exact ⟨f₁, hf₁, (prop_1_3 M hGA (wLowDisc M β) hmeas hfin f₁ hf₁ hACOI).1, hlim⟩
  · intro hWS
    obtain ⟨f₀, hf₀, hPhi₀, hgl, hlu⟩ : ∃ f₁ : S → A, ∃ hf₁ : IsStationary M f₁,
        (∀ x, Phi M (statPolicy hf₁) x = gStar M) ∧ gStar M = gLower M ∧
          gLower M = gUpper M := hWS.elim hWex hSex
    have hm := tendsto_m M hlu
    rw [← hgl] at hm
    refine ⟨hm, fun x => ?_⟩
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · rw [← hm.liminf_eq]
      apply Filter.liminf_le_liminf (Eventually.of_forall fun β => ?_)
      exact mul_le_mul_right (iInf_le _ x) _
    · calc limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * vβ M β x) (𝓝[<] 1)
          ≤ limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M (statPolicy hf₀) β x)
              (𝓝[<] 1) := by
            apply Filter.limsup_le_limsup (Eventually.of_forall fun β => ?_)
            exact mul_le_mul_right
              (iInf_le (fun π : {π : Policy S A // Admissible M π} => Jbeta M π.1 β x)
                ⟨statPolicy hf₀, admissible_stat M hf₀⟩) _
        _ ≤ Phi M (statPolicy hf₀) x :=
            (lemma_1_2 M).1 _ (admissible_stat M hf₀) x
        _ = gStar M := hPhi₀ x
