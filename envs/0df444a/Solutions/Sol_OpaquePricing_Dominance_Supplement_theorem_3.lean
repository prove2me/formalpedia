-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:07.71349+00:00
-- url     : https://prove2.me/submissions/88a9d1a4-25e1-426a-a220-afc9a5b1aadd

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing
import Definitions.Def_OpaquePricing_Dominance_Supplement_ExampleLaw

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1) (hex : Exchangeable μ) :
    optDP μ ≤ ENNReal.ofReal (1 + Real.log N) * optSP μ ∧
    optOPQ μ α ≤ (N : ENNReal) * optSP μ ∧
    ∃ ρ : Measure (Fin N → ℝ), ρ = exampleLaw N ∧ IsProbabilityMeasure ρ ∧
      Exchangeable ρ ∧ (∀ᵐ v ∂ρ, ∀ i, 0 ≤ v i) ∧
      0 < optDP ρ ∧ optDP ρ < ⊤ ∧
      0 < optSP ρ ∧ optSP ρ ≤ 2 ∧
      ENNReal.ofReal (α * N) ≤ optOPQ ρ α ∧
      ENNReal.ofReal (α / 2 * ((N : ℝ) / (1 + Real.log N))) * optDP ρ ≤
        optOPQ ρ α := by
          have P2 : ∀ μ : Measure (Fin N → ℝ), optOPQ μ α ≤ (N : ENNReal) * optSP μ := by
            intro μ
            have hSP : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} ≤ optSP μ := by
              intro t ht
              exact le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i}) t ht
            have hBm : ∀ t : ℝ, MeasurableSet {v : Fin N → ℝ | ∃ i, t ≤ v i} := by
              intro t
              have : {v : Fin N → ℝ | ∃ i, t ≤ v i} = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by ext v; simp
              rw [this]
              exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
            have key : ∀ (val : (Fin N → ℝ) → Finset (Fin N) → ℝ),
                (∀ v S, S.Nonempty → ∃ i ∈ S, val v S ≤ v i) →
                ∀ p : ℝ, ∀ q : ℕ → ℝ, 0 ≤ p → (∀ k, 0 ≤ q k) →
                ∫⁻ v, ENNReal.ofReal (opqRevenue val p q v) ∂μ ≤ (N : ENNReal) * optSP μ := by
              intro val hval p q hp hq
              set c : Fin N → ℝ := fun k => if k.val + 1 = 1 then p else q (k.val + 1) with hc
              have hc0 : ∀ k, 0 ≤ c k := by
                intro k; simp only [hc]; split_ifs
                · exact hp
                · exact hq _
              have hpt : ∀ v, ENNReal.ofReal (opqRevenue val p q v) ≤
                  ∑ k : Fin N, ({v : Fin N → ℝ | ∃ i, c k ≤ v i}).indicator (fun _ => ENNReal.ofReal (c k)) v := by
                intro v
                unfold opqRevenue menuRevenue
                dsimp only
                split_ifs with h
                · obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' h (opqPrice p q)
                  rw [hSeq]
                  simp only [Finset.mem_filter, opqOptions, Finset.mem_univ, true_and] at hS
                  obtain ⟨hne, hu, -⟩ := hS
                  obtain ⟨i, hi, hvi⟩ := hval v S hne
                  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hne
                  have hcardN : S.card ≤ N := by
                    simpa using Finset.card_le_univ S
                  set k : Fin N := ⟨S.card - 1, by omega⟩ with hk
                  have hck : c k = opqPrice p q S := by
                    simp only [hc, hk, opqPrice]
                    have : S.card - 1 + 1 = S.card := by omega
                    rw [this]
                  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ({v : Fin N → ℝ | ∃ i, c k ≤ v i}).indicator (fun _ => ENNReal.ofReal (c k)) v) (fun _ _ => bot_le) (Finset.mem_univ k))
                  have hmem : v ∈ {v : Fin N → ℝ | ∃ i, c k ≤ v i} := ⟨i, by rw [hck]; linarith⟩
                  rw [Set.indicator_of_mem hmem, hck]
                · simp
              calc ∫⁻ v, ENNReal.ofReal (opqRevenue val p q v) ∂μ
                  ≤ ∫⁻ v, ∑ k : Fin N, ({v : Fin N → ℝ | ∃ i, c k ≤ v i}).indicator (fun _ => ENNReal.ofReal (c k)) v ∂μ :=
                    lintegral_mono hpt
                _ = ∑ k : Fin N, ∫⁻ v, ({v : Fin N → ℝ | ∃ i, c k ≤ v i}).indicator (fun _ => ENNReal.ofReal (c k)) v ∂μ := by
                    rw [lintegral_finsetSum]
                    intro k _
                    exact measurable_const.indicator (hBm _)
                _ = ∑ k : Fin N, ENNReal.ofReal (c k) * μ {v | ∃ i, c k ≤ v i} := by
                    refine Finset.sum_congr rfl fun k _ => ?_
                    rw [lintegral_indicator_const (hBm _)]
                _ ≤ ∑ _k : Fin N, optSP μ := Finset.sum_le_sum fun k _ => hSP _ (hc0 k)
                _ = (N : ENNReal) * optSP μ := by simp
            have hpess : ∀ (v : Fin N → ℝ) (S : Finset (Fin N)), S.Nonempty → ∃ i ∈ S, pessValue v S ≤ v i := by
              intro v S hS
              obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hS v
              refine ⟨i, hi, ?_⟩
              simp [pessValue, hS, he]
            have hrn : ∀ (v : Fin N → ℝ) (S : Finset (Fin N)), S.Nonempty → ∃ i ∈ S, rnValue v S ≤ v i := by
              intro v S hS
              have hpos : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
              apply Finset.exists_le_of_sum_le hS
              simp only [Finset.sum_const, nsmul_eq_mul, rnValue]
              rw [mul_div_cancel₀ _ hpos.ne']
            unfold optOPQ
            refine iSup_le fun p => iSup_le fun q => iSup_le fun hpq => ?_
            unfold expOPQ
            calc ENNReal.ofReal α * (∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ) +
                ENNReal.ofReal (1 - α) * (∫⁻ v, ENNReal.ofReal (opqRevenue rnValue p q v) ∂μ)
                ≤ ENNReal.ofReal α * ((N : ENNReal) * optSP μ) + ENNReal.ofReal (1 - α) * ((N : ENNReal) * optSP μ) := by
                  gcongr
                  · exact key _ hpess p q hpq.1 hpq.2
                  · exact key _ hrn p q hpq.1 hpq.2
              _ = (N : ENNReal) * optSP μ := by
                  rw [← add_mul, ← ENNReal.ofReal_add hα.1 (by linarith [hα.2])]
                  simp
          have P1 : ∀ μ : Measure (Fin N → ℝ), IsProbabilityMeasure μ → (∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) →
              Exchangeable μ → optDP μ ≤ ENNReal.ofReal (1 + Real.log N) * optSP μ := by
            intro μ _ _ hex
            have hSP : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i} ≤ optSP μ := by
              intro t ht
              exact le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i}) t ht
            unfold optDP
            refine iSup₂_le fun p hp => ?_
            classical
            set L : Fin N → Finset (Fin N) := fun i => Finset.univ.filter (fun j => p j ≤ p i) with hL
            set T : Fin N → (Fin N → ℝ) → Finset (Fin N) :=
              fun i v => (L i).filter (fun j => ∀ k ∈ L i, v k ≤ v j) with hT
            set f : Fin N → Fin N → (Fin N → ℝ) → ENNReal :=
              fun i x v => if x ∈ T i v ∧ p i ≤ v x then ((T i v).card : ENNReal)⁻¹ else 0 with hf
            have hmemL : ∀ i j, j ∈ L i ↔ p j ≤ p i := by intro i j; simp [hL]
            have hmemT : ∀ i v j, j ∈ T i v ↔ p j ≤ p i ∧ ∀ k, p k ≤ p i → v k ≤ v j := by
              intro i v j; simp [hT, hL]
            -- (B) measurability
            have hBm : ∀ i x, MeasurableSet {v : Fin N → ℝ | ∀ k, p k ≤ p i → v k ≤ v x} := by
              intro i x
              have : {v : Fin N → ℝ | ∀ k, p k ≤ p i → v k ≤ v x} =
                  ⋂ k, ⋂ (_ : p k ≤ p i), {v : Fin N → ℝ | v k ≤ v x} := by ext v; simp
              rw [this]
              exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
                measurableSet_le (measurable_pi_apply k) (measurable_pi_apply x)
            have hmeas : ∀ i x, Measurable (f i x) := by
              intro i x
              have hA : MeasurableSet {v : Fin N → ℝ | x ∈ T i v ∧ p i ≤ v x} := by
                have : {v : Fin N → ℝ | x ∈ T i v ∧ p i ≤ v x} =
                    {v | p x ≤ p i} ∩ ({v : Fin N → ℝ | ∀ k, p k ≤ p i → v k ≤ v x} ∩ {v | p i ≤ v x}) := by
                  ext v; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hmemT, and_assoc]
                rw [this]
                exact (MeasurableSet.const _).inter ((hBm i x).inter (measurableSet_le measurable_const (measurable_pi_apply x)))
              have hcardf : ∀ v, (T i v).card = ∑ j ∈ L i, if v ∈ {v : Fin N → ℝ | ∀ k, p k ≤ p i → v k ≤ v j} then 1 else 0 := by
                intro v
                rw [hT]; dsimp only
                rw [Finset.card_filter]
                refine Finset.sum_congr rfl fun j _ => ?_
                congr 1
                simp only [Set.mem_setOf_eq, hmemL]
              have hg : Measurable (fun v : Fin N → ℝ => ((T i v).card : ENNReal)⁻¹) := by
                simp_rw [hcardf]
                exact (measurable_from_nat (f := fun n : ℕ => ((n : ENNReal))⁻¹)).comp
                  (Finset.measurable_sum _ fun j _ => Measurable.ite (hBm i j) measurable_const measurable_const)
              exact Measurable.ite hA hg measurable_const
            -- (A) pointwise bound
            have hA : ∀ v, ENNReal.ofReal (dpRevenue p v) ≤ ∑ i, ENNReal.ofReal (p i) * f i i v := by
              intro v
              unfold dpRevenue menuRevenue
              dsimp only
              split_ifs with h
              · obtain ⟨a, ha, haeq⟩ := Finset.exists_mem_eq_sup' h p
                rw [haeq]
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                obtain ⟨ha0, hamax⟩ := ha
                have haT : a ∈ T a v := by
                  rw [hmemT]
                  refine ⟨le_rfl, fun k hk => ?_⟩
                  have := hamax k (by simp)
                  linarith
                have hTeq : ∀ i ∈ T a v, p i = p a ∧ v i = v a := by
                  intro i hi
                  rw [hmemT] at hi
                  have h1 := hi.2 a le_rfl
                  have h2 := ((hmemT a v a).mp haT).2 i hi.1
                  have h3 := hamax i (by simp)
                  refine ⟨by linarith [hi.1], by linarith⟩
                have hLeq : ∀ i ∈ T a v, L i = L a := by
                  intro i hi; ext j; rw [hmemL, hmemL, (hTeq i hi).1]
                have hfi : ∀ i ∈ T a v, f i i v = ((T a v).card : ENNReal)⁻¹ := by
                  intro i hi
                  have hTi : T i v = T a v := by rw [hT]; dsimp only; rw [hLeq i hi]
                  simp only [hf]
                  rw [if_pos ⟨by rw [hTi]; exact hi, by rw [(hTeq i hi).1, (hTeq i hi).2]; linarith⟩, hTi]
                have hcne : ((T a v).card : ENNReal) ≠ 0 := by
                  simpa using Finset.card_pos.mpr ⟨a, haT⟩ |>.ne'
                calc ENNReal.ofReal (p a) = ∑ i ∈ T a v, ENNReal.ofReal (p i) * f i i v := by
                      rw [Finset.sum_congr rfl fun i hi => by rw [hfi i hi, (hTeq i hi).1]]
                      rw [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_assoc, ENNReal.inv_mul_cancel hcne (by simp), mul_one]
                  _ ≤ ∑ i, ENNReal.ofReal (p i) * f i i v :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)
              · simp
            -- (C) exchangeability
            have hC : ∀ i, ∀ x ∈ L i, ∫⁻ v, f i x v ∂μ = ∫⁻ v, f i i v ∂μ := by
              intro i x hx
              set τ := Equiv.swap x i with hτ
              have hφ : Measurable (fun v : Fin N → ℝ => v ∘ τ) :=
                measurable_pi_lambda _ fun j => measurable_pi_apply (τ j)
              have hτL : ∀ k, p (τ k) ≤ p i ↔ p k ≤ p i := by
                have hx' : p x ≤ p i := (hmemL i x).mp hx
                intro k
                rw [hτ, Equiv.swap_apply_def]
                split_ifs with h1 h2
                · subst h1; exact ⟨fun _ => hx', fun _ => le_rfl⟩
                · subst h2; exact ⟨fun _ => le_rfl, fun _ => hx'⟩
                · exact Iff.rfl
              have hpt : ∀ v, f i i (v ∘ τ) = f i x v := by
                intro v
                have hTτ : T i (v ∘ τ) = (T i v).map τ.toEmbedding := by
                  ext j
                  rw [Finset.mem_map_equiv, hmemT, hmemT, hτ, Equiv.symm_swap]
                  rw [← hτ]
                  constructor
                  · rintro ⟨h1, h2⟩
                    refine ⟨(hτL j).mpr h1, fun k hk => ?_⟩
                    have := h2 (τ k) ((hτL k).mpr hk)
                    simpa [hτ, Function.comp] using this
                  · rintro ⟨h1, h2⟩
                    refine ⟨(hτL j).mp h1, fun k hk => ?_⟩
                    have := h2 (τ k) ((hτL k).mpr hk)
                    simpa [Function.comp] using this
                have hτi : τ i = x := by rw [hτ, Equiv.swap_apply_right]
                have hsy : τ.symm i = x := by rw [hτ, Equiv.symm_swap, Equiv.swap_apply_right]
                have hcardτ : (T i (v ∘ τ)).card = (T i v).card := by rw [hTτ, Finset.card_map]
                have hmemτ : i ∈ T i (v ∘ τ) ↔ x ∈ T i v := by rw [hTτ, Finset.mem_map_equiv, hsy]
                have hvτ : (v ∘ τ) i = v x := by rw [Function.comp_apply, hτi]
                show (if i ∈ T i (v ∘ τ) ∧ p i ≤ (v ∘ τ) i then ((T i (v ∘ τ)).card : ENNReal)⁻¹ else 0) =
                  (if x ∈ T i v ∧ p i ≤ v x then ((T i v).card : ENNReal)⁻¹ else 0)
                rw [hcardτ, hvτ]
                simp only [hmemτ]
              calc ∫⁻ v, f i x v ∂μ = ∫⁻ v, f i i (v ∘ τ) ∂μ := by simp_rw [hpt]
                _ = ∫⁻ v, f i i v ∂(μ.map (fun v => v ∘ τ)) := (lintegral_map (hmeas i i) hφ).symm
                _ = ∫⁻ v, f i i v ∂μ := by rw [hex τ]
            -- (D)
            have hD : ∀ i v, ∑ x ∈ L i, f i x v ≤ {v : Fin N → ℝ | ∃ j, p i ≤ v j}.indicator 1 v := by
              intro i v
              by_cases hv : ∃ j, p i ≤ v j
              · rw [Set.indicator_of_mem (show v ∈ {v : Fin N → ℝ | ∃ j, p i ≤ v j} from hv), Pi.one_apply]
                calc ∑ x ∈ L i, f i x v ≤ ∑ x ∈ L i, if x ∈ T i v then ((T i v).card : ENNReal)⁻¹ else 0 := by
                      refine Finset.sum_le_sum fun x _ => ?_
                      show (if x ∈ T i v ∧ p i ≤ v x then ((T i v).card : ENNReal)⁻¹ else 0) ≤ _
                      by_cases h1 : x ∈ T i v
                      · rw [if_pos h1]; split_ifs <;> simp
                      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
                  _ = ((T i v).card : ENNReal) * ((T i v).card : ENNReal)⁻¹ := by
                      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _), Finset.sum_const,
                        nsmul_eq_mul]
                  _ ≤ 1 := ENNReal.mul_inv_le_one _
              · refine le_trans (le_of_eq ?_) bot_le
                refine Finset.sum_eq_zero fun x _ => ?_
                simp only [hf]
                rw [if_neg]
                rintro ⟨-, h⟩
                exact hv ⟨x, h⟩
            have hSm : ∀ t : ℝ, MeasurableSet {v : Fin N → ℝ | ∃ i, t ≤ v i} := by
              intro t
              have : {v : Fin N → ℝ | ∃ i, t ≤ v i} = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by ext v; simp
              rw [this]
              exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
            -- (E),(F)
            have hF : ∀ i, ENNReal.ofReal (p i) * ∫⁻ v, f i i v ∂μ ≤ ((L i).card : ENNReal)⁻¹ * optSP μ := by
              intro i
              have hE : ((L i).card : ENNReal) * ∫⁻ v, f i i v ∂μ ≤ μ {v | ∃ j, p i ≤ v j} := by
                calc ((L i).card : ENNReal) * ∫⁻ v, f i i v ∂μ = ∑ x ∈ L i, ∫⁻ v, f i x v ∂μ := by
                      rw [Finset.sum_congr rfl fun x hx => hC i x hx, Finset.sum_const, nsmul_eq_mul]
                  _ = ∫⁻ v, ∑ x ∈ L i, f i x v ∂μ := (lintegral_finsetSum _ fun x _ => hmeas i x).symm
                  _ ≤ ∫⁻ v, {v : Fin N → ℝ | ∃ j, p i ≤ v j}.indicator 1 v ∂μ := lintegral_mono fun v => hD i v
                  _ = μ {v | ∃ j, p i ≤ v j} := lintegral_indicator_one (hSm _)
              have hc0 : ((L i).card : ENNReal) ≠ 0 := by
                have : 0 < (L i).card := Finset.card_pos.mpr ⟨i, (hmemL i i).mpr le_rfl⟩
                exact_mod_cast this.ne'
              calc ENNReal.ofReal (p i) * ∫⁻ v, f i i v ∂μ
                  = ((L i).card : ENNReal)⁻¹ * (ENNReal.ofReal (p i) * (((L i).card : ENNReal) * ∫⁻ v, f i i v ∂μ)) := by
                    rw [mul_left_comm, ← mul_assoc ((L i).card : ENNReal)⁻¹, ENNReal.inv_mul_cancel hc0 (by simp), one_mul]
                _ ≤ ((L i).card : ENNReal)⁻¹ * (ENNReal.ofReal (p i) * μ {v | ∃ j, p i ≤ v j}) := by gcongr
                _ ≤ ((L i).card : ENNReal)⁻¹ * optSP μ := by gcongr; exact hSP _ (hp i)
            -- (G)
            have hG : ∑ i, ((L i).card : ENNReal)⁻¹ ≤ ENNReal.ofReal (1 + Real.log N) := by
              set σ := Tuple.sort p with hσ
              have hmono : Monotone (p ∘ σ) := Tuple.monotone_sort p
              rw [← Equiv.sum_comp σ]
              have hk : ∀ k : Fin N, ((L (σ k)).card : ENNReal)⁻¹ ≤ ENNReal.ofReal ((k.val + 1 : ℝ)⁻¹) := by
                intro k
                have hsub : (Finset.Iic k).map σ.toEmbedding ⊆ L (σ k) := by
                  intro j hj
                  rw [Finset.mem_map_equiv, Finset.mem_Iic] at hj
                  rw [hmemL]
                  have := hmono hj
                  simp only [Function.comp, Equiv.apply_symm_apply] at this
                  exact this
                have hc := Finset.card_le_card hsub
                simp only [Finset.card_map, Fin.card_Iic] at hc
                rw [ENNReal.ofReal_inv_of_pos (by positivity)]
                apply ENNReal.inv_le_inv.mpr
                rw [show ((k.val : ℝ) + 1) = ((k.val + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
                exact_mod_cast hc
              calc ∑ k, ((L (σ k)).card : ENNReal)⁻¹ ≤ ∑ k : Fin N, ENNReal.ofReal ((k.val + 1 : ℝ)⁻¹) :=
                    Finset.sum_le_sum fun k _ => hk k
                _ = ENNReal.ofReal (∑ k : Fin N, ((k.val + 1 : ℝ)⁻¹)) :=
                    (ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity).symm
                _ ≤ ENNReal.ofReal (1 + Real.log N) := by
                    apply ENNReal.ofReal_le_ofReal
                    have hh := harmonic_le_one_add_log N
                    have : ((harmonic N : ℚ) : ℝ) = ∑ k : Fin N, ((k.val + 1 : ℝ)⁻¹) := by
                      rw [harmonic, Fin.sum_univ_eq_sum_range (fun k => ((k + 1 : ℝ))⁻¹)]
                      push_cast; rfl
                    linarith
            unfold expDP
            calc ∫⁻ v, ENNReal.ofReal (dpRevenue p v) ∂μ ≤ ∫⁻ v, ∑ i, ENNReal.ofReal (p i) * f i i v ∂μ :=
                  lintegral_mono hA
              _ = ∑ i, ENNReal.ofReal (p i) * ∫⁻ v, f i i v ∂μ := by
                  rw [lintegral_finsetSum _ fun i _ => (hmeas i i).const_mul _]
                  exact Finset.sum_congr rfl fun i _ => lintegral_const_mul _ (hmeas i i)
              _ ≤ ∑ i, ((L i).card : ENNReal)⁻¹ * optSP μ := Finset.sum_le_sum fun i _ => hF i
              _ = (∑ i, ((L i).card : ENNReal)⁻¹) * optSP μ := (Finset.sum_mul _ _ _).symm
              _ ≤ ENNReal.ofReal (1 + Real.log N) * optSP μ := by gcongr
          have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
          set ρ := exampleLaw N with hρdef
          set x : Fin N → Fin N → ℝ := fun k i => if i.val ≤ k.val then (2 : ℝ) ^ (N - k.val) else 0 with hx
          have hρapp : ∀ S, MeasurableSet S → ρ S = ∑ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ *
              ((Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ * ∑ σ : Equiv.Perm (Fin N), S.indicator 1 (x k ∘ σ)) +
              (ENNReal.ofReal ((2:ℝ) ^ N))⁻¹ * S.indicator 1 (fun _ => (1:ℝ)) := by
            intro S hS
            simp only [hρdef, exampleLaw, permutationLaw, Measure.add_apply, Measure.coe_finset_sum, Measure.smul_apply,
              Finset.sum_apply, Measure.dirac_apply' _ hS, smul_eq_mul, hx]
          have hnn : ∀ k (σ : Equiv.Perm (Fin N)) i, 0 ≤ (x k ∘ σ) i := by
            intro k σ i; simp only [hx, Function.comp]; split_ifs <;> positivity
          have hρnn : ∀ᵐ v ∂ρ, ∀ i, 0 ≤ v i := by
            have hm : MeasurableSet {v : Fin N → ℝ | ¬ ∀ i, 0 ≤ v i} := by
              have : {v : Fin N → ℝ | ¬ ∀ i, 0 ≤ v i} = ⋃ i, {v : Fin N → ℝ | v i < 0} := by ext v; simp
              rw [this]; exact MeasurableSet.iUnion fun i => measurableSet_lt (measurable_pi_apply i) measurable_const
            rw [ae_iff, hρapp _ hm]
            have h1 : ∀ k (σ : Equiv.Perm (Fin N)), {v : Fin N → ℝ | ¬ ∀ i, 0 ≤ v i}.indicator 1 (x k ∘ σ) = (0 : ENNReal) := by
              intro k σ
              exact Set.indicator_of_notMem (by simpa using hnn k σ) _
            have h2 : {v : Fin N → ℝ | ¬ ∀ i, 0 ≤ v i}.indicator 1 (fun _ => (1:ℝ)) = (0 : ENNReal) :=
              Set.indicator_of_notMem (by simp) _
            simp only [h1, h2, Finset.sum_const_zero, mul_zero, add_zero]
          have hcard : (Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ * (Fintype.card (Equiv.Perm (Fin N)) : ENNReal) = 1 :=
            ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (by simp)
          have hg : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((2:ℝ) ^ (n - k))⁻¹ + ((2:ℝ) ^ n)⁻¹ = 1 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Finset.sum_range_succ]
              have : ∑ k ∈ Finset.range n, ((2:ℝ) ^ (n + 1 - k))⁻¹ = 2⁻¹ * ∑ k ∈ Finset.range n, ((2:ℝ) ^ (n - k))⁻¹ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k hk => ?_
                have hk' : k < n := Finset.mem_range.mp hk
                rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ, mul_inv, mul_comm]
              rw [this, show n + 1 - n = 1 by omega]
              have h2 : ∑ k ∈ Finset.range n, ((2:ℝ) ^ (n - k))⁻¹ = 1 - ((2:ℝ) ^ n)⁻¹ := by linarith
              rw [h2, pow_succ, mul_inv]; ring
          have hgeom : ∑ k : Fin N, ((2:ℝ) ^ (N - k.val))⁻¹ + ((2:ℝ) ^ N)⁻¹ = 1 := by
            rw [Fin.sum_univ_eq_sum_range (fun k => ((2:ℝ) ^ (N - k))⁻¹)]
            exact hg N
          have hρprob : IsProbabilityMeasure ρ := by
            constructor
            rw [hρapp _ MeasurableSet.univ]
            simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
            have h1 : ENNReal.ofReal (∑ k : Fin N, ((2:ℝ) ^ (N - k.val))⁻¹ + ((2:ℝ) ^ N)⁻¹) = 1 := by
              rw [hgeom, ENNReal.ofReal_one]
            rw [← h1, ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => by positivity) (by positivity),
              ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
            congr 1
            · refine Finset.sum_congr rfl fun k _ => ?_
              rw [ENNReal.ofReal_inv_of_pos (by positivity)]
            · rw [ENNReal.ofReal_inv_of_pos (by positivity)]
          have hρex : Exchangeable ρ := by
            intro σ
            have hmeas : Measurable (fun v : Fin N → ℝ => v ∘ σ) :=
              measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
            ext S hS
            rw [Measure.map_apply hmeas hS, hρapp _ (hmeas hS), hρapp _ hS]
            have hind : ∀ y : Fin N → ℝ, ((fun v : Fin N → ℝ => v ∘ σ) ⁻¹' S).indicator (1 : (Fin N → ℝ) → ENNReal) y =
                S.indicator 1 (y ∘ σ) := by
              intro y
              by_cases hy : y ∘ σ ∈ S
              · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ (fun v : Fin N → ℝ => v ∘ σ) ⁻¹' S from hy)]; rfl
              · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ (fun v : Fin N → ℝ => v ∘ σ) ⁻¹' S from hy)]
            simp only [hind]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            congr 2
            exact Equiv.sum_comp (Equiv.mulRight σ) (fun τ => S.indicator 1 (x k ∘ τ))
          have hSPpos : 0 < optSP ρ := by
            have hS1m : MeasurableSet {v : Fin N → ℝ | ∃ i, (1:ℝ) ≤ v i} := by
              have : {v : Fin N → ℝ | ∃ i, (1:ℝ) ≤ v i} = ⋃ i, {v : Fin N → ℝ | (1:ℝ) ≤ v i} := by ext v; simp
              rw [this]
              exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
            have hpos : 0 < ρ {v : Fin N → ℝ | ∃ i, (1:ℝ) ≤ v i} := by
              rw [hρapp _ hS1m]
              have hmem : (fun _ : Fin N => (1:ℝ)) ∈ {v : Fin N → ℝ | ∃ i, (1:ℝ) ≤ v i} :=
                ⟨⟨0, by omega⟩, le_refl _⟩
              refine lt_of_lt_of_le ?_ le_add_self
              rw [Set.indicator_of_mem hmem]
              simp
            have hle : expSP ρ 1 ≤ optSP ρ :=
              le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) => expSP ρ t) 1 zero_le_one
            refine lt_of_lt_of_le ?_ hle
            simpa [expSP] using hpos
          have hρint : ∀ f : (Fin N → ℝ) → ENNReal, ∫⁻ v, f v ∂ρ = ∑ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ *
              ((Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ * ∑ σ : Equiv.Perm (Fin N), f (x k ∘ σ)) +
              (ENNReal.ofReal ((2:ℝ) ^ N))⁻¹ * f (fun _ => (1:ℝ)) := by
            intro f
            simp only [hρdef, exampleLaw, permutationLaw, lintegral_add_measure, lintegral_finset_sum_measure,
              lintegral_smul_measure, lintegral_dirac, hx, smul_eq_mul]
          have hcancel : ∀ a : ENNReal, (Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ *
              ((Fintype.card (Equiv.Perm (Fin N)) : ENNReal) * a) = a := by
            intro a; rw [← mul_assoc, hcard, one_mul]
          have hSP2 : optSP ρ ≤ 2 := by
            unfold optSP
            refine iSup₂_le fun t ht => ?_
            rcases ht.eq_or_lt with h0 | htpos
            · simp [expSP, ← h0]
            unfold expSP
            have hm : MeasurableSet {v : Fin N → ℝ | ∃ i, t ≤ v i} := by
              have : {v : Fin N → ℝ | ∃ i, t ≤ v i} = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by ext v; simp
              rw [this]
              exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
            have hind : ∀ k (σ : Equiv.Perm (Fin N)), {v : Fin N → ℝ | ∃ i, t ≤ v i}.indicator
                (1 : (Fin N → ℝ) → ENNReal) (x k ∘ σ) = if t ≤ (2:ℝ)^(N - k.val) then 1 else 0 := by
              intro k σ
              by_cases h : t ≤ (2:ℝ)^(N - k.val)
              · rw [if_pos h, Set.indicator_of_mem]
                · rfl
                refine ⟨σ.symm ⟨0, by omega⟩, ?_⟩
                simp only [hx, Function.comp, Equiv.apply_symm_apply]
                rw [if_pos (Nat.zero_le _)]; exact h
              · rw [if_neg h, Set.indicator_of_notMem]
                rintro ⟨i, hi⟩
                simp only [hx, Function.comp] at hi
                split_ifs at hi <;> linarith
            have hind1 : {v : Fin N → ℝ | ∃ i, t ≤ v i}.indicator (1 : (Fin N → ℝ) → ENNReal)
                (fun _ => (1:ℝ)) = if t ≤ 1 then 1 else 0 := by
              by_cases h : t ≤ 1
              · rw [if_pos h, Set.indicator_of_mem (show (fun _ => (1:ℝ)) ∈ {v : Fin N → ℝ | ∃ i, t ≤ v i} from
                  ⟨⟨0, by omega⟩, h⟩)]; rfl
              · rw [if_neg h, Set.indicator_of_notMem]; rintro ⟨i, hi⟩; exact h hi
            rw [hρapp _ hm]
            simp only [hind, hind1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcancel]
            set h : ℕ → ℝ := fun m => if t ≤ (2:ℝ)^m then ((2:ℝ)^m)⁻¹ else 0 with hh
            have hh0 : ∀ m, 0 ≤ h m := by intro m; simp only [hh]; split_ifs <;> positivity
            have hterm : ∀ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ *
                (if t ≤ (2:ℝ)^(N-k.val) then 1 else 0) ≤ ENNReal.ofReal (h (N - k.val)) := by
              intro k
              simp only [hh]
              split_ifs
              · rw [mul_one, ENNReal.ofReal_inv_of_pos (by positivity)]
              · simp
            have hterm1 : (ENNReal.ofReal ((2:ℝ) ^ N))⁻¹ * (if t ≤ 1 then 1 else 0) ≤ ENNReal.ofReal (h 0) := by
              simp only [hh, pow_zero]
              split_ifs
              · simp only [mul_one, inv_one, ENNReal.ofReal_one]
                exact ENNReal.inv_le_one.2 (ENNReal.one_le_ofReal.2 (one_le_pow₀ (by norm_num)))
              · simp
            set G : ℕ → ℝ := fun m => min (2 / t) (2 / 2 ^ m) with hG
            have hhG : ∀ m, h m ≤ G m - G (m+1) := by
              intro m
              have ha : (0:ℝ) < 2 ^ m := by positivity
              simp only [hh, hG, pow_succ]
              split_ifs with hle
              · have e1 : min (2/t) (2 / 2^m) = 2 / 2^m :=
                  min_eq_right (div_le_div_of_nonneg_left (by norm_num) htpos hle)
                have e2 : min (2/t) (2 / (2^m * 2)) = 2 / (2^m*2) :=
                  min_eq_right (div_le_div_of_nonneg_left (by norm_num) htpos (by linarith))
                rw [e1, e2]; apply le_of_eq; field_simp; ring
              · have : min (2/t) (2 / (2^m*2)) ≤ min (2/t) (2/2^m) :=
                  min_le_min le_rfl (div_le_div_of_nonneg_left (by norm_num) ha (by linarith))
                linarith
            have hsumG : ∑ m ∈ Finset.range (N+1), h m ≤ G 0 - G (N+1) := by
              rw [← Finset.sum_range_sub']; exact Finset.sum_le_sum fun m _ => hhG m
            have hreidx : ∑ k : Fin N, h (N - k.val) + h 0 = ∑ m ∈ Finset.range (N+1), h m := by
              have hr := Finset.sum_range_reflect (fun i => h (i+1)) N
              try simp only at hr
              rw [Finset.sum_range_succ', Fin.sum_univ_eq_sum_range (fun k => h (N - k)), ← hr]
              congr 1
              refine Finset.sum_congr rfl fun j hj => ?_
              have := Finset.mem_range.mp hj
              congr 1; omega
            have hreal : t * (∑ k : Fin N, h (N - k.val) + h 0) ≤ 2 := by
              have hG1 : 0 ≤ G (N+1) := le_min (by positivity) (by positivity)
              have hG0 : G 0 ≤ 2 / t := min_le_left _ _
              have : ∑ k : Fin N, h (N - k.val) + h 0 ≤ 2 / t := by linarith
              calc t * (∑ k : Fin N, h (N - k.val) + h 0) ≤ t * (2 / t) := by gcongr
                _ = 2 := by field_simp
            have hR : ∑ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ * (if t ≤ (2:ℝ)^(N-k.val) then 1 else 0) +
                (ENNReal.ofReal ((2:ℝ) ^ N))⁻¹ * (if t ≤ 1 then 1 else 0) ≤
                ENNReal.ofReal (∑ k : Fin N, h (N - k.val) + h 0) := by
              rw [ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => hh0 _) (hh0 _),
                ENNReal.ofReal_sum_of_nonneg fun _ _ => hh0 _]
              exact add_le_add (Finset.sum_le_sum fun k _ => hterm k) hterm1
            calc ENNReal.ofReal t * _ ≤ ENNReal.ofReal t * ENNReal.ofReal (∑ k : Fin N, h (N - k.val) + h 0) :=
                  mul_le_mul' le_rfl hR
              _ = ENNReal.ofReal (t * (∑ k : Fin N, h (N - k.val) + h 0)) := (ENNReal.ofReal_mul ht).symm
              _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hreal
              _ = 2 := by simp
          have hOPQ : ENNReal.ofReal (α * N) ≤ optOPQ ρ α := by
            set p : ℝ := 2 ^ N with hp
            set q : ℕ → ℝ := fun s => 2 ^ (N + 1 - s) with hq
            have hpq : 0 ≤ p ∧ ∀ k, 0 ≤ q k := ⟨by positivity, fun k => by positivity⟩
            have hprice : ∀ S : Finset (Fin N), opqPrice p q S = 2 ^ (N + 1 - S.card) ∨ S.card = 0 := by
              intro S
              unfold opqPrice
              split_ifs with h
              · left; rw [h, hp]; simp
              · left; rfl
            have hprice' : ∀ S : Finset (Fin N), S.Nonempty → opqPrice p q S = 2 ^ (N + 1 - S.card) := by
              intro S hS
              rcases hprice S with h | h
              · exact h
              · exact absurd h (Finset.card_pos.mpr hS).ne'
            have hrev : ∀ k : Fin N, ∀ σ : Equiv.Perm (Fin N), ENNReal.ofReal ((2:ℝ) ^ (N - k.val)) ≤
                ENNReal.ofReal (opqRevenue pessValue p q (x k ∘ σ)) := by
              intro k σ
              apply ENNReal.ofReal_le_ofReal
              set H : Finset (Fin N) := (Finset.Iic k).map σ.symm.toEmbedding with hH
              have hmemH : ∀ i, i ∈ H ↔ σ i ≤ k := by
                intro i; simp [hH, Finset.mem_map_equiv]
              have hHcard : H.card = k.val + 1 := by simp [hH]
              have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
              have hvH : ∀ i ∈ H, (x k ∘ σ) i = 2 ^ (N - k.val) := by
                intro i hi; simp only [hx, Function.comp]; rw [if_pos (Fin.le_def.mp ((hmemH i).mp hi))]
              have hvle : ∀ i, (x k ∘ σ) i ≤ 2 ^ (N - k.val) := by
                intro i; simp only [hx, Function.comp]; split_ifs
                · exact le_rfl
                · positivity
              have hvnot : ∀ i, i ∉ H → (x k ∘ σ) i = 0 := by
                intro i hi; simp only [hx, Function.comp]
                rw [if_neg (fun h => hi ((hmemH i).mpr (Fin.le_def.mpr h)))]
              have hpessle : ∀ S' : Finset (Fin N), ∀ i ∈ S', pessValue (x k ∘ σ) S' ≤ (x k ∘ σ) i := by
                intro S' i hi
                unfold pessValue; rw [dif_pos ⟨i, hi⟩]; exact Finset.inf'_le _ hi
              have hpessH : pessValue (x k ∘ σ) H = 2 ^ (N - k.val) := by
                unfold pessValue; rw [dif_pos hHne]
                obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hHne (x k ∘ σ)
                rw [he, hvH i hi]
              have hpriceH : opqPrice p q H = 2 ^ (N - k.val) := by
                rw [hprice' H hHne, hHcard]; congr 1; omega
              have hHopt : H ∈ opqOptions N := by simp [opqOptions, hHne]
              have hwin : 0 ≤ pessValue (x k ∘ σ) H - opqPrice p q H ∧
                  ∀ S' ∈ opqOptions N, pessValue (x k ∘ σ) S' - opqPrice p q S' ≤
                    pessValue (x k ∘ σ) H - opqPrice p q H := by
                refine ⟨by rw [hpessH, hpriceH]; simp, ?_⟩
                intro S' hS'
                have hS'ne : S'.Nonempty := by simpa [opqOptions] using hS'
                rw [hpessH, hpriceH, sub_self, sub_nonpos]
                obtain ⟨i0, hi0⟩ := hS'ne
                by_cases hsub : S' ⊆ H
                · have hc : S'.card ≤ k.val + 1 := hHcard ▸ Finset.card_le_card hsub
                  calc pessValue (x k ∘ σ) S' ≤ (x k ∘ σ) i0 := hpessle S' i0 hi0
                    _ ≤ 2 ^ (N - k.val) := hvle i0
                    _ ≤ 2 ^ (N + 1 - S'.card) := pow_le_pow_right₀ (by norm_num) (by omega)
                    _ = opqPrice p q S' := (hprice' S' ⟨i0, hi0⟩).symm
                · obtain ⟨i, hi, hiH⟩ := Finset.not_subset.mp hsub
                  calc pessValue (x k ∘ σ) S' ≤ (x k ∘ σ) i := hpessle S' i hi
                    _ = 0 := hvnot i hiH
                    _ ≤ opqPrice p q S' := by rw [hprice' S' ⟨i, hi⟩]; positivity
              unfold opqRevenue menuRevenue
              dsimp only
              split_ifs with hne
              · rw [← hpriceH]
                exact Finset.le_sup' (opqPrice p q) (by simp only [Finset.mem_filter]; exact ⟨hHopt, hwin⟩)
              · exact absurd ⟨H, by simp only [Finset.mem_filter]; exact ⟨hHopt, hwin⟩⟩ hne
            have hint : (N : ENNReal) ≤ ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂ρ := by
              rw [hρint]
              refine le_trans ?_ le_self_add
              have hone : ∀ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ *
                  ((Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ *
                    ∑ σ : Equiv.Perm (Fin N), ENNReal.ofReal ((2:ℝ) ^ (N - k.val))) = 1 := by
                intro k
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcancel]
                exact ENNReal.inv_mul_cancel (by simp) ENNReal.ofReal_ne_top
              calc (N : ENNReal) = ∑ k : Fin N, (ENNReal.ofReal ((2:ℝ) ^ (N - k.val)))⁻¹ *
                    ((Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ *
                      ∑ σ : Equiv.Perm (Fin N), ENNReal.ofReal ((2:ℝ) ^ (N - k.val))) := by
                    rw [Finset.sum_congr rfl fun k _ => hone k]; simp
                _ ≤ _ := by
                    refine Finset.sum_le_sum fun k _ => ?_
                    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (Finset.sum_le_sum fun σ _ => hrev k σ))
            calc ENNReal.ofReal (α * N) = ENNReal.ofReal α * (N : ENNReal) := by
                  rw [ENNReal.ofReal_mul hα.1, ENNReal.ofReal_natCast]
              _ ≤ ENNReal.ofReal α * ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂ρ := by gcongr
              _ ≤ expOPQ ρ α p q := by unfold expOPQ; exact le_self_add
              _ ≤ optOPQ ρ α := by
                  unfold optOPQ
                  exact le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le hpq le_rfl))
          have hDPpos : 0 < optDP ρ := by
            have hrev : dpRevenue (fun _ : Fin N => (1/2 : ℝ)) (fun _ => 1) = 1/2 := by
              have hne : (Finset.univ.filter (fun o : Fin N => 0 ≤ (1:ℝ) - 1/2 ∧
                  ∀ o' ∈ (Finset.univ : Finset (Fin N)), (1:ℝ) - 1/2 ≤ 1 - 1/2)).Nonempty :=
                ⟨⟨0, by omega⟩, by simp; norm_num⟩
              unfold dpRevenue menuRevenue
              simp only
              rw [dif_pos hne]
              exact Finset.sup'_const hne _
            have hle : expDP ρ (fun _ => 1/2) ≤ optDP ρ :=
              le_iSup₂ (f := fun (p : Fin N → ℝ) (_ : ∀ i, 0 ≤ p i) => expDP ρ p) (fun _ => 1/2) (fun _ => by norm_num)
            refine lt_of_lt_of_le ?_ hle
            unfold expDP
            rw [hρdef, exampleLaw, lintegral_add_measure]
            refine lt_of_lt_of_le ?_ le_add_self
            rw [lintegral_smul_measure, lintegral_dirac, hrev]
            simp
          have hDP : optDP ρ ≤ ENNReal.ofReal (1 + Real.log N) * 2 :=
            le_trans (P1 ρ hρprob hρnn hρex) (by gcongr)
          refine ⟨P1 μ inferInstance hμ hex, P2 μ, ρ, rfl, hρprob, hρex, hρnn, hDPpos, ?_, hSPpos, hSP2, hOPQ, ?_⟩
          · exact lt_of_le_of_lt hDP (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num))
          · refine le_trans ?_ hOPQ
            calc ENNReal.ofReal (α / 2 * ((N : ℝ) / (1 + Real.log N))) * optDP ρ
                ≤ ENNReal.ofReal (α / 2 * ((N : ℝ) / (1 + Real.log N))) * (ENNReal.ofReal (1 + Real.log N) * 2) := by
                  gcongr
              _ = ENNReal.ofReal (α * N) := by
                  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul
                    (by have := hα.1; positivity)]
                  congr 1
                  field_simp
