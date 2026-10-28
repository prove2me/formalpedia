-- Prove2me | solution 1 for ScheduledQueue.Diffusion.count_lln
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:49:19.267165+00:00
-- url     : https://prove2.me/submissions/7118b9d4-cbae-4dad-bed7-6c7911ee4427

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

open Set Filter Topology MeasureTheory ProbabilityTheory

/-- counting bounds for the arrivals in `(0, T]` -/
lemma SQL_bounds (h u ε T : ℝ) (hh : 0 < h) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1 / 2) (hT : 0 ≤ T) (x : ℤ → ℝ) (E : Set ℤ) (hE : E.Finite)
    (hx : ∀ i, i ∉ E → |x i| ≤ ε * ((i.natAbs : ℕ) : ℝ) * h) :
    ({i : ℤ | (i : ℝ) * h + h * u + x i ∈ Ioc 0 T}.ncard : ℝ) ≤ E.ncard + T / (h * (1 - ε)) + 3 ∧
    (T - h) / (h * (1 + ε)) - 1 - E.ncard ≤ ({i : ℤ | (i : ℝ) * h + h * u + x i ∈ Ioc 0 T}.ncard : ℝ) := by
  set S := {i : ℤ | (i : ℝ) * h + h * u + x i ∈ Ioc 0 T} with hS
  have hq : 0 < h * (1 - ε) := by nlinarith
  have hq' : 0 < h * (1 + ε) := by nlinarith
  have hhu0 : 0 ≤ h * u := by positivity
  have hhu1 : h * u ≤ h := by nlinarith
  -- absolute value bound in terms of the integer
  have habs : ∀ i : ℤ, ((i.natAbs : ℕ) : ℝ) = |(i : ℝ)| := by
    intro i; rw [Nat.cast_natAbs, Int.cast_abs]
  set K : ℤ := ⌊T / (h * (1 - ε))⌋ with hK
  have hK0 : 0 ≤ K := Int.floor_nonneg.mpr (div_nonneg hT hq.le)
  have hsub : S ⊆ E ∪ ↑(Finset.Icc (-2 : ℤ) K) := by
    intro i hi
    by_cases hiE : i ∈ E
    · exact Or.inl hiE
    right
    have hxi := hx i hiE
    rw [habs] at hxi
    have hxi' := abs_le.mp hxi
    simp only [hS, mem_setOf_eq, mem_Ioc] at hi
    simp only [Finset.coe_Icc, mem_Icc]
    rcases le_or_gt 0 i with hi0 | hi0
    · have hi0' : (0 : ℝ) ≤ i := by exact_mod_cast hi0
      rw [abs_of_nonneg hi0'] at hxi'
      refine ⟨by omega, ?_⟩
      rw [hK, Int.le_floor, le_div_iff₀ hq]
      nlinarith
    · have hi0' : (i : ℝ) < 0 := by exact_mod_cast hi0
      rw [abs_of_neg hi0'] at hxi'
      refine ⟨?_, by omega⟩
      by_contra hc
      have : i ≤ -3 := by omega
      have : (i : ℝ) ≤ -3 := by exact_mod_cast this
      nlinarith
  have hfinS : S.Finite := (hE.union (Finset.finite_toSet _)).subset hsub
  constructor
  · have h1 : S.ncard ≤ E.ncard + (Finset.Icc (-2 : ℤ) K).card := by
      calc S.ncard ≤ (E ∪ ↑(Finset.Icc (-2 : ℤ) K)).ncard :=
            Set.ncard_le_ncard hsub (hE.union (Finset.finite_toSet _))
        _ ≤ E.ncard + (↑(Finset.Icc (-2 : ℤ) K) : Set ℤ).ncard := Set.ncard_union_le _ _
        _ = E.ncard + (Finset.Icc (-2 : ℤ) K).card := by rw [Set.ncard_coe_finset]
    have h2 : ((Finset.Icc (-2 : ℤ) K).card : ℝ) = (K : ℝ) + 3 := by
      rw [Int.card_Icc]
      have : (K + 1 - -2).toNat = ((K + 3).toNat) := by congr 1; ring
      rw [this]
      have h3 : (((K + 3).toNat : ℕ) : ℤ) = K + 3 := Int.toNat_of_nonneg (by omega)
      have h4 : (((K + 3).toNat : ℕ) : ℝ) = ((((K + 3).toNat : ℕ) : ℤ) : ℝ) := by norm_cast
      rw [h4, h3]; push_cast; ring
    have h5 : (K : ℝ) ≤ T / (h * (1 - ε)) := Int.floor_le _
    have h6 : (S.ncard : ℝ) ≤ E.ncard + ((Finset.Icc (-2 : ℤ) K).card : ℝ) := by exact_mod_cast h1
    linarith
  · set K' : ℤ := ⌊(T - h) / (h * (1 + ε))⌋ with hK'
    have hsub2 : (↑(Finset.Icc (1 : ℤ) K') : Set ℤ) ⊆ (S ∪ E) := by
      intro i hi
      by_cases hiE : i ∈ E
      · exact Or.inr hiE
      left
      simp only [Finset.coe_Icc, mem_Icc] at hi
      have hxi := hx i hiE
      rw [habs] at hxi
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
      rw [abs_of_nonneg (show (0:ℝ) ≤ (i:ℝ) by linarith)] at hxi
      have hxi' := abs_le.mp hxi
      have hiK : (i : ℝ) ≤ (T - h) / (h * (1 + ε)) := by
        have := hi.2; rw [hK', Int.le_floor] at this; exact this
      rw [le_div_iff₀ hq'] at hiK
      simp only [hS, mem_setOf_eq, mem_Ioc]
      constructor <;> nlinarith
    have h1 : (Finset.Icc (1 : ℤ) K').card ≤ S.ncard + E.ncard := by
      calc (Finset.Icc (1 : ℤ) K').card = (↑(Finset.Icc (1 : ℤ) K') : Set ℤ).ncard :=
            (Set.ncard_coe_finset _).symm
        _ ≤ (S ∪ E).ncard := Set.ncard_le_ncard hsub2 (hfinS.union hE)
        _ ≤ S.ncard + E.ncard := Set.ncard_union_le _ _
    have h2 : (K' : ℝ) ≤ ((Finset.Icc (1 : ℤ) K').card : ℝ) := by
      rw [Int.card_Icc]
      have : K' + 1 - 1 = K' := by ring
      rw [this]
      have h3 : K' ≤ ((K'.toNat : ℕ) : ℤ) := Int.self_le_toNat K'
      have h4 : ((K'.toNat : ℕ) : ℝ) = (((K'.toNat : ℕ) : ℤ) : ℝ) := by norm_cast
      rw [h4]; exact_mod_cast h3
    have h5 : (T - h) / (h * (1 + ε)) - 1 < (K' : ℝ) := Int.sub_one_lt_floor _
    have h6 : ((Finset.Icc (1 : ℤ) K').card : ℝ) ≤ S.ncard + E.ncard := by exact_mod_cast h1
    linarith

lemma SQL_limit (h : ℝ) (hh : 0 < h) (f : ℝ → ℝ)
    (hb : ∀ m : ℕ, ∃ C : ℝ, ∀ T, 0 ≤ T →
      f T ≤ C + T / (h * (1 - 1 / ((m : ℝ) + 2))) ∧
      (T - h) / (h * (1 + 1 / ((m : ℝ) + 2))) - C ≤ f T) :
    Tendsto (fun T => f T / T) atTop (𝓝 (1 / h)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    set a' := (max a 0 + 1 / h) / 2 with ha'
    have hmax : max a 0 < 1 / h := max_lt ha (by positivity)
    have haa' : a < a' := by have := le_max_left a 0; linarith
    have ha'0 : 0 < a' := by have := le_max_right a 0; linarith
    have ha'h : a' < 1 / h := by linarith
    have hha' : h * a' < 1 := by rw [lt_div_iff₀ hh] at ha'h; linarith
    set δ := 1 / (h * a') - 1 with hδ
    have hδ0 : 0 < δ := by
      rw [hδ, sub_pos, lt_div_iff₀ (by positivity)]; linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ0
    obtain ⟨C, hC⟩ := hb n
    set ε := 1 / ((n : ℝ) + 2) with hε
    have hε0 : 0 < ε := by positivity
    have hεn : ε < 1 / ((n : ℝ) + 1) := by
      rw [hε]; apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hεδ : ε < δ := lt_trans hεn hn
    set q := 1 / (h * (1 + ε)) with hq
    have hpos : 0 < h * (1 + ε) := by positivity
    have hqa : a' < q := by
      rw [hq, lt_div_iff₀ hpos]
      have : h * (1 + ε) < h * (1 + δ) := by nlinarith
      have h2 : h * (1 + δ) = 1 / a' := by
        rw [hδ]; field_simp; ring
      have h3 : a' * (h * (1 + δ)) = 1 := by rw [h2] <;> field_simp
      nlinarith
    set D := 1 / (1 + ε) + C with hD
    filter_upwards [eventually_ge_atTop (max 1 ((|D| + 1) / (q - a')))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : (|D| + 1) / (q - a') ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := by linarith
    rw [div_le_iff₀ (by linarith)] at hT2
    have hlow := (hC T hTpos.le).2
    have heq : (T - h) / (h * (1 + 1 / ((n : ℝ) + 2))) = T * q - 1 / (1 + ε) := by
      rw [hq, hε]; field_simp <;> ring
    rw [heq] at hlow
    rw [lt_div_iff₀ hTpos]
    have := le_abs_self D
    nlinarith
  · intro b hb'
    have hhb : 1 < h * b := by
      have := hb'; rw [gt_iff_lt, div_lt_iff₀ hh] at this; linarith
    have hb0 : 0 < b := by
      by_contra hc; push Not at hc; nlinarith
    set δ := 1 - 1 / (h * b) with hδ
    have hδ0 : 0 < δ := by
      rw [hδ, sub_pos, div_lt_one (by positivity)]; exact hhb
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ0
    obtain ⟨C, hC⟩ := hb n
    set ε := 1 / ((n : ℝ) + 2) with hε
    have hε0 : 0 < ε := by positivity
    have hεn : ε < 1 / ((n : ℝ) + 1) := by
      rw [hε]; apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hεδ : ε < δ := lt_trans hεn hn
    have hpos' : 0 < 1 / (h * b) := by positivity
    have hδ1 : δ < 1 := by rw [hδ]; linarith
    have hε1 : ε < 1 := by linarith
    set q := 1 / (h * (1 - ε)) with hq
    have hpos : 0 < h * (1 - ε) := by nlinarith
    have hqb : q < b := by
      rw [hq, div_lt_iff₀ hpos]
      have : h * (1 - δ) < h * (1 - ε) := by nlinarith
      have h2 : h * (1 - δ) = 1 / b := by
        rw [hδ]; field_simp; ring
      have h3 : b * (h * (1 - δ)) = 1 := by rw [h2] <;> field_simp
      nlinarith
    filter_upwards [eventually_ge_atTop (max 1 ((|C| + 1) / (b - q)))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : (|C| + 1) / (b - q) ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : 0 < T := by linarith
    rw [div_le_iff₀ (by linarith)] at hT2
    have hup := (hC T hTpos.le).1
    have heq : T / (h * (1 - 1 / ((n : ℝ) + 2))) = T * q := by
      rw [hq, hε]; field_simp
    rw [heq] at hup
    rw [div_lt_iff₀ hTpos]
    have := le_abs_self C
    nlinarith

lemma SQL_ae_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (c : ℝ) (hc : 0 < c) :
    ∀ᵐ ω ∂P, {i : ℤ | ((i.natAbs : ℕ) : ℝ) < c * |ξ i ω|}.Finite := by
  apply ae_finite_setOfPred_mem (s := fun i : ℤ => {ω | ((i.natAbs : ℕ) : ℝ) < c * |ξ i ω|})
  set X : Ω → ℝ := fun ω => c * |ξ 0 ω| with hX
  set g : ℕ → ENNReal := fun n => P {ω | X ω ∈ Ioi (n : ℝ)} with hg
  have hfun : Measurable (fun x : ℝ => c * |x|) := by fun_prop
  have heq : ∀ i : ℤ, P {ω | ((i.natAbs : ℕ) : ℝ) < c * |ξ i ω|} = g i.natAbs := by
    intro i
    have hid := (hin.identDistrib i).comp hfun
    have := hid.measure_mem_eq (s := Ioi ((i.natAbs : ℕ) : ℝ)) measurableSet_Ioi
    simp only [hg, hX]; exact this
  simp_rw [heq]
  have hint : Integrable X P := (hin.integrable.abs).const_mul c
  have hnn : 0 ≤ X := fun ω => by simp only [hX]; positivity
  have hsum : ∑' j : ℕ, P {ω | X ω ∈ Ioi (j : ℝ)} < ⊤ := by
    letI : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hint hnn
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' n : ℕ, g ((n : ℤ).natAbs) = ∑' n : ℕ, g n := by simp
  have h2 : ∑' n : ℕ, g ((-(n + 1 : ℤ)).natAbs) ≤ ∑' n : ℕ, g n := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    have : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
    rw [this]
    refine measure_mono (fun ω hω => ?_)
    simp only [mem_setOf_eq, mem_Ioi] at hω ⊢
    push_cast at hω; linarith
  rw [h1]
  exact (ENNReal.add_lt_top.mpr ⟨hsum, lt_of_le_of_lt h2 hsum⟩).ne

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ s : ℝ, 0 ≤ s → ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ => (ScheduledQueue.Stability.count h ξ U (t * s) ω : ℝ) / t) atTop (𝓝 (s / h)) := by
  intro s hs
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0:ℝ) 1 := by
    rw [ae_iff]
    rw [hin.uniform.measure_eq (p := fun v => v ∉ Icc (0:ℝ) 1) measurableSet_Icc.compl]
    show (volume.restrict (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp
  have hF : ∀ᵐ ω ∂P, ∀ m : ℕ,
      {i : ℤ | ((i.natAbs : ℕ) : ℝ) < (((m : ℝ) + 2) / h) * |ξ i ω|}.Finite :=
    ae_all_iff.2 (fun m => SQL_ae_fin P ξ U hin _ (by positivity))
  filter_upwards [hU, hF] with ω hu hf
  have hmain : Tendsto (fun T => (ScheduledQueue.Stability.count h ξ U T ω : ℝ) / T) atTop
      (𝓝 (1 / h)) := by
    apply SQL_limit h hh
    intro m
    set E := {i : ℤ | ((i.natAbs : ℕ) : ℝ) < (((m : ℝ) + 2) / h) * |ξ i ω|} with hE
    refine ⟨E.ncard + 3, fun T hT => ?_⟩
    have hx : ∀ i, i ∉ E → |ξ i ω| ≤ 1 / ((m : ℝ) + 2) * ((i.natAbs : ℕ) : ℝ) * h := by
      intro i hi
      simp only [hE, mem_setOf_eq, not_lt] at hi
      rw [div_mul_eq_mul_div, div_le_iff₀ hh] at hi
      rw [one_div_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have hm2 : (0:ℝ) < (m : ℝ) + 2 := by positivity
    have hε1 : 1 / ((m : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [Nat.cast_nonneg (α := ℝ) m]
    have hb := SQL_bounds h (U ω) (1 / ((m : ℝ) + 2)) T hh hu.1 hu.2 (by positivity) hε1 hT
      (fun i => ξ i ω) E (hf m) hx
    have hc : (ScheduledQueue.Stability.count h ξ U T ω : ℝ) =
        ({i : ℤ | (i : ℝ) * h + h * U ω + ξ i ω ∈ Ioc 0 T}.ncard : ℝ) := rfl
    rw [hc]
    constructor <;> linarith [hb.1, hb.2]
  rcases hs.eq_or_lt with rfl | hs0
  · have : ∀ t : ℝ, (ScheduledQueue.Stability.count h ξ U (t * 0) ω : ℝ) / t = 0 := by
      intro t
      simp [ScheduledQueue.Stability.count]
    simp only [this, zero_div]
    exact tendsto_const_nhds
  · have h1 := hmain.comp (tendsto_id.atTop_mul_const hs0)
    have h2 := h1.const_mul s
    rw [mul_one_div] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply, id]
    field_simp
