-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:10:54.227049+00:00
-- url     : https://prove2.me/submissions/d03ff3ab-de3e-4651-99b2-faab7930c815
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
import Theorems.Thm_OfflineCensoredPricing_Identifiability_theorem_2
import Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_6

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPThm1Aux

lemma valid_d2acd {K : ℕ} [NeZero K] (P : Public K) (h : P.plo ≤ P.phi) :
    Valid P (d2acd P) := by
  intro Nv S
  have hlo : P.plo ∈ Icc P.plo P.phi := ⟨le_rfl, h⟩
  unfold d2acd
  split_ifs with h0
  · exact hlo
  · unfold pD2ACD
    split_ifs with hne
    · have hsub : pD2ACDSet P S ⊆ Icc P.plo P.phi := fun q hq => hq.1
      obtain ⟨q, hq⟩ := hne
      exact ⟨le_trans (hsub hq).1 (le_csSup ⟨P.phi, fun x hx => (hsub hx).2⟩ hq),
        csSup_le ⟨q, hq⟩ (fun x hx => (hsub hx).2)⟩
    · exact hlo

lemma gam_pos {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) : 0 < gam I := by
  obtain ⟨hP, -, -, -, -, -, -, -, -, -, -, -, hgam, -⟩ := hI
  have i : Fin K := 0
  have hle : I.yh i + I.b * I.p i ≤ lam I :=
    le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i
  have h1 := hgam i
  unfold gammaI at h1
  unfold gam
  exact lt_of_lt_of_le h1 (measureReal_mono (Iio_subset_Iio hle))

lemma bad_subset {K : ℕ} (I : Instance K) (Nv : Fin K → ℕ) (i : Fin K) :
    {ω : Sample K Nv | ¬ 0 < gammaHat I.toPublic (sales I ω) i} ⊆
      (fun ω : Sample K Nv => ω i) ⁻¹' (univ.pi fun _ => Ici (I.yh i + I.b * I.p i)) := by
  intro ω hω
  simp only [mem_preimage, mem_univ_pi, mem_Ici]
  intro j
  by_contra hlt
  push_neg at hlt
  apply hω
  unfold gammaHat
  have hmem : j ∈ Finset.univ.filter (fun j => sales I ω i j < I.yh i) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show min (ω i j - I.b * I.p i) (I.yh i) < I.yh i
    exact min_lt_iff.2 (Or.inl (by linarith))
  have hcard : 0 < (Finset.univ.filter (fun j => sales I ω i j < I.yh i)).card :=
    Finset.card_pos.2 ⟨j, hmem⟩
  have hN : 0 < Nv i := Fin.pos j
  exact div_pos (by exact_mod_cast hcard) (by exact_mod_cast hN)

lemma bad_measure {K : ℕ} (I : Instance K) [IsProbabilityMeasure I.μξ] (Nv : Fin K → ℕ)
    (i : Fin K) :
    dataLaw I Nv {ω : Sample K Nv | ¬ 0 < gammaHat I.toPublic (sales I ω) i} ≤
      (I.μξ (Ici (I.yh i + I.b * I.p i))) ^ (Nv i) := by
  refine le_trans (measure_mono (bad_subset I Nv i)) (le_of_eq ?_)
  have hmp : MeasurePreserving (Function.eval i) (dataLaw I Nv)
      (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
    unfold dataLaw
    exact measurePreserving_eval _ i
  have hms : MeasurableSet (univ.pi fun _ : Fin (Nv i) => Ici (I.yh i + I.b * I.p i)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ici)
  rw [show (fun ω : Sample K Nv => ω i) = Function.eval i from rfl,
    hmp.measure_preimage hms.nullMeasurableSet, Measure.pi_pi]
  simp

lemma r_lt_one {K : ℕ} (I : Instance K) [IsProbabilityMeasure I.μξ] (i : Fin K)
    (h : 0 < gammaI I i) : I.μξ (Ici (I.yh i + I.b * I.p i)) < 1 := by
  rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
  have hne : I.μξ (Iio (I.yh i + I.b * I.p i)) ≠ 0 := by
    intro h0
    unfold gammaI at h
    rw [measureReal_def, h0] at h
    simp at h
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne

end OCPThm1Aux

open OCPThm1Aux in
theorem solution {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) :
    (Valid I.toPublic (d2acd I.toPublic) ∧
      (pStarMax I = pStarMin I → NearOptimal I (d2acd I.toPublic))) ∧
    (pStarMax I ≠ pStarMin I →
      0 < gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ∧
      ∀ q ∈ Icc I.plo I.phi,
        gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
          worstLoss I q) ∧
    (Identifiable I ↔ pStarMax I = pStarMin I) := by
  obtain ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, hinj, hpi, hyh, hneg, hgam, hA1⟩ := hI
  haveI := hP
  have hvalid : Valid I.toPublic (d2acd I.toPublic) := valid_d2acd I.toPublic hlohi.le
  -- near-optimality from Theorem 2 plus the vanishing probability of `γ̂ᵢ = 0`
  have hnear : pStarMax I = pStarMin I → NearOptimal I (d2acd I.toPublic) := by
    intro heq ε hε η hη
    set r : Fin K → ENNReal := fun i => I.μξ (Ici (I.yh i + I.b * I.p i)) with hr
    have hr1 : ∀ i, r i < 1 := fun i => r_lt_one I i (hgam i)
    have htend : Filter.Tendsto (fun n : ℕ => ∑ i, r i ^ n) Filter.atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin K))
        (fun i _ => ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (hr1 i))
      simpa using this
    have hη2 : (0 : ENNReal) < ENNReal.ofReal (η / 2) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 (htend.eventually (gt_mem_nhds hη2))
    set δ : ℝ := min (η / 2) (1 / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine ⟨max N1 ⌈Cthm2 I * (1 / (ε / 2) ^ 2) * Real.log (8 * K / δ)⌉₊, ?_⟩
    intro Nv hNv
    have hNv1 : N1 ≤ Nmin Nv := le_trans (le_max_left _ _) hNv
    have hNv2 : Cthm2 I * (1 / (ε / 2) ^ 2) * Real.log (8 * K / δ) ≤ (Nmin Nv : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hNv)
    have hT2 := theorem_2 I ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, hinj, hpi, hyh, hneg,
      hgam, hA1⟩ heq (half_pos hε) hδ0 hδ1 Nv hNv2
    have hsub : {ω | ε ≤ worstLoss I (d2acd I.toPublic Nv (sales I ω))} ⊆
        {ω | ε / 2 < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
          ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ∪
        ⋃ i, {ω : Sample K Nv | ¬ 0 < gammaHat I.toPublic (sales I ω) i} := by
      intro ω hω
      by_cases hall : ∀ i, 0 < gammaHat I.toPublic (sales I ω) i
      · left
        exact ⟨by simp only [mem_setOf_eq] at hω; linarith, hall⟩
      · right
        push_neg at hall
        obtain ⟨i, hi⟩ := hall
        exact mem_iUnion.2 ⟨i, by simpa using hi⟩
    have hbad : dataLaw I Nv (⋃ i, {ω : Sample K Nv | ¬ 0 < gammaHat I.toPublic (sales I ω) i})
        ≤ ENNReal.ofReal (η / 2) := by
      refine le_trans (measure_iUnion_fintype_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => bad_measure I Nv i)) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (hN1 N1 le_rfl).le
      have hle : N1 ≤ Nv i := le_trans hNv1 (ciInf_le (Finite.bddBelow_range Nv) i)
      exact pow_le_pow_right_of_le_one' (hr1 i).le hle
    calc dataLaw I Nv {ω | ε ≤ worstLoss I (d2acd I.toPublic Nv (sales I ω))}
        ≤ dataLaw I Nv ({ω | ε / 2 < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
            ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ∪
            ⋃ i, {ω : Sample K Nv | ¬ 0 < gammaHat I.toPublic (sales I ω) i}) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal (η / 2) :=
          le_trans (measure_union_le _ _) (add_le_add hT2 hbad)
      _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_rfl
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  -- the lower bound from Proposition 6
  have hlow : pStarMax I ≠ pStarMin I →
      0 < gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ∧
      ∀ q ∈ Icc I.plo I.phi,
        gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
          worstLoss I q := by
    intro hne
    refine ⟨?_, (proposition_6 I ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, hinj, hpi, hyh,
      hneg, hgam, hA1⟩ hne).2⟩
    have hg := gam_pos I ⟨hP, hy, hplo, hlohi, hblo, hbb, hbhi, hK, hinj, hpi, hyh, hneg, hgam,
      hA1⟩
    have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
    have hd : 0 < (pStarMax I - pStarMin I) ^ 2 := by
      have : pStarMax I - pStarMin I ≠ 0 := sub_ne_zero.2 hne
      positivity
    have hs : 0 < (Real.sqrt (gam I) + 1) ^ 2 := by positivity
    exact mul_pos (div_pos (mul_pos hg hb) hs) hd
  refine ⟨⟨hvalid, hnear⟩, hlow, ⟨?_, fun h => ⟨d2acd I.toPublic, hvalid, hnear h⟩⟩⟩
  rintro ⟨A, hAv, hAn⟩
  by_contra hne
  obtain ⟨hc, hbound⟩ := hlow hne
  obtain ⟨N0, hN0⟩ := hAn _ hc (1 / 2) (by norm_num)
  have hNmin : Nmin (fun _ : Fin K => N0) = N0 := by
    unfold Nmin
    exact ciInf_const
  have h := hN0 (fun _ => N0) hNmin.ge
  have huniv : {ω : Sample K (fun _ => N0) |
      gam I * I.b / (Real.sqrt (gam I) + 1) ^ 2 * (pStarMax I - pStarMin I) ^ 2 ≤
        worstLoss I (A (fun _ => N0) (sales I ω))} = univ := by
    ext ω
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact hbound _ (hAv _ _)
  rw [huniv] at h
  haveI : IsProbabilityMeasure (dataLaw I (fun _ : Fin K => N0)) := by
    unfold dataLaw
    infer_instance
  rw [measure_univ] at h
  have : ENNReal.ofReal (1 / 2) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  exact absurd h (not_le.2 this)
