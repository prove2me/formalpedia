-- Prove2me | solution 1 for SubsampVB.Consist.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:55:18.655195+00:00
-- url     : https://prove2.me/submissions/49a4b506-fd49-4566-8075-3199c8d66e58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubsampVB_Consist_Setting
import Theorems.Thm_SubsampVB_Consist_theorem_7
import Theorems.Thm_SubsampVB_Consist_proposition_1
import Theorems.Thm_SubsampVB_Consist_theorem_2_mse_rate

open MeasureTheory Filter Finset ProbabilityTheory SubsampVB.Consist

universe u v

namespace SVBThm2Aux

lemma empirical_isProb {α : Type u} [MeasurableSpace α] {k : ℕ} (z : Fin k → α)
    (hk : k ≠ 0) : IsProbabilityMeasure (empirical z) := by
  constructor
  simp only [empirical, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)

lemma memLp4_of_mu4 {Q : Measure ℝ} [IsProbabilityMeasure Q] (c : ℝ)
    (h : ∫⁻ y, ‖y - c‖ₑ ^ 4 ∂Q < ⊤) : MemLp (fun y : ℝ => y) 4 Q := by
  have h1 : MemLp (fun y : ℝ => y - c) 4 Q := by
    refine ⟨(measurable_id.sub_const c).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have e : ((4 : ENNReal).toReal) = ((4 : ℕ) : ℝ) := by norm_num
    simp_rw [e, ENNReal.rpow_natCast]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne
  have h2 := h1.add (memLp_const c)
  refine h2.ae_eq (Filter.Eventually.of_forall (fun y => ?_))
  simp

lemma sq_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 4 μ) : MemLp (fun x => f x ^ 2) 2 μ := by
  have h := hf.norm_rpow_div 2
  have e : (4 : ENNReal) / 2 = 2 :=
    ((ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 (by norm_num)).symm
  rw [e] at h
  refine h.ae_eq (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs, sq_abs]

lemma sigmaHat_memLp {B R : ℕ} (μ : Measure (Fin B → Fin R → ℝ)) (θ : ℝ)
    (h : ∀ b r, MemLp (fun Y : Fin B → Fin R → ℝ => Y b r) 4 μ) :
    MemLp (fun Y => sigmaHatSVB θ Y) 2 μ := by
  have hgm : ∀ b, MemLp (fun Y => groupMean Y b) 4 μ := fun b => by
    unfold groupMean
    exact (memLp_finsetSum univ (fun r _ => h b r)).const_mul _
  have hGM : MemLp (fun Y => grandMean Y) 4 μ := by
    unfold grandMean
    exact (memLp_finsetSum univ (fun b _ => hgm b)).const_mul _
  have h1 : MemLp (fun Y => ∑ b, (groupMean Y b - grandMean Y) ^ 2) 2 μ :=
    memLp_finsetSum univ (fun b _ => sq_memLp ((hgm b).sub hGM))
  have h2 : MemLp (fun Y => withinV Y) 2 μ := by
    unfold withinV
    exact (memLp_finsetSum univ (fun b _ => memLp_finsetSum univ
      (fun r _ => sq_memLp ((h b r).sub (hgm b))))).const_mul _
  unfold sigmaHatSVB
  exact ((h1.const_mul _).sub (h2.mul_const _)).const_mul _

variable {m : ℕ} {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]

/-- Conditional Chebyshev bound for the relative-error event. -/
lemma outProb_le {B R : ℕ} (simLaw : Inputs Ξ → Measure ℝ) {N s : Fin m → ℕ}
    (x : Sample Ξ N) (θ c0 σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
    (hprob : ∀ J : Resample N s, IsProbabilityMeasure (simLaw (Fbar univ J x)))
    (hL4 : ∀ J : Resample N s, MemLp (fun y : ℝ => y) 4 (simLaw (Fbar univ J x)))
    (hclose : |c0 / σ - 1| < ε / 2) :
    outProb (B := B) (R := R) (s := s) simLaw x {Y | ε < |sigmaHatSVB θ Y / σ - 1|} ≤
      ((Fintype.card (Fin B → Resample N s) : ℝ)⁻¹ *
        ∑ I : Fin B → Resample N s,
          ∫ Y, (sigmaHatSVB θ Y - c0) ^ 2 ∂(outputLaw (R := R) simLaw I x)) /
        ((ε * σ / 2) ^ 2) := by
  have ht : 0 < (ε * σ / 2) ^ 2 := by positivity
  unfold outProb
  rw [mul_div_assoc, Finset.sum_div]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun I _ => ?_)) (by positivity)
  haveI : ∀ b, IsProbabilityMeasure (simLaw (Fbar univ (I b) x)) := fun b => hprob (I b)
  haveI hμ : IsProbabilityMeasure (outputLaw (R := R) simLaw I x) := by
    unfold outputLaw; infer_instance
  have hcoord : ∀ b r, MemLp (fun Y : Fin B → Fin R → ℝ => Y b r) 4
      (outputLaw (R := R) simLaw I x) := by
    intro b r
    have h1 : MemLp (fun z : Fin R → ℝ => z r) 4
        (Measure.pi (fun _ : Fin R => simLaw (Fbar univ (I b) x))) :=
      (hL4 (I b)).comp_measurePreserving (measurePreserving_eval _ r)
    exact h1.comp_measurePreserving (measurePreserving_eval _ b)
  have hL2 := (sigmaHat_memLp _ θ hcoord).sub (memLp_const c0)
  have hint : Integrable (fun Y => (sigmaHatSVB θ Y - c0) ^ 2)
      (outputLaw (R := R) simLaw I x) := hL2.integrable_sq
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun Y => sq_nonneg (sigmaHatSVB θ Y - c0))) hint
    ((ε * σ / 2) ^ 2)
  have hsub : {Y : Fin B → Fin R → ℝ | ε < |sigmaHatSVB θ Y / σ - 1|} ⊆
      {Y | (ε * σ / 2) ^ 2 ≤ (sigmaHatSVB θ Y - c0) ^ 2} := by
    intro Y hY
    simp only [Set.mem_ofPred_eq] at hY ⊢
    have hsplit : sigmaHatSVB θ Y / σ - 1 = (sigmaHatSVB θ Y - c0) / σ + (c0 / σ - 1) := by
      field_simp; ring
    have htri := abs_add_le ((sigmaHatSVB θ Y - c0) / σ) (c0 / σ - 1)
    rw [← hsplit, abs_div, abs_of_pos hσ] at htri
    have hk : ε / 2 < |sigmaHatSVB θ Y - c0| / σ := by linarith
    rw [lt_div_iff₀ hσ] at hk
    rw [← sq_abs (sigmaHatSVB θ Y - c0)]
    have h0 : 0 ≤ ε * σ / 2 := by positivity
    nlinarith
  have hmono : (outputLaw (R := R) simLaw I x).real
      {Y : Fin B → Fin R → ℝ | ε < |sigmaHatSVB θ Y / σ - 1|} ≤
      (outputLaw (R := R) simLaw I x).real
        {Y | (ε * σ / 2) ^ 2 ≤ (sigmaHatSVB θ Y - c0) ^ 2} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [le_div_iff₀ ht]
  have : ((outputLaw (R := R) simLaw I x)
      {Y : Fin B → Fin R → ℝ | ε < |sigmaHatSVB θ Y / σ - 1|}).toReal =
      (outputLaw (R := R) simLaw I x).real
      {Y : Fin B → Fin R → ℝ | ε < |sigmaHatSVB θ Y / σ - 1|} := rfl
  rw [this]
  nlinarith

end SVBThm2Aux

open SVBThm2Aux in
theorem solution
    {m : ℕ} [NeZero m] {Ξ : Fin m → Type u} [∀ i, MeasurableSpace (Ξ i)]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Inputs Ξ) [∀ i, IsProbabilityMeasure (F i)]
    (S : ∀ i, Set (Ξ i)) (ψ : Inputs Ξ → ℝ)
    (g : Inputs Ξ → ∀ i, Ξ i → ℝ) (simLaw : Inputs Ξ → Measure ℝ)
    (X : ∀ i : Fin m, ℕ → Ω → Ξ i) (n : ℕ → Fin m → ℕ)
    (θ : ℕ → ℝ) (B R : ℕ → ℕ)
    (hS : ∀ i, MeasurableSet (S i) ∧ F i (S i)ᶜ = 0)
    (hData : IIDData P F X) (hOracle : SimOracle ψ simLaw)
    (hTauFinite : Integrable (fun y => (y - ψ F) ^ 2) (simLaw F))
    (hA1 : A1 n) (hA2 : A2 F S ψ g) (hA3 : A3 P F ψ g X n)
    (hA4 : A4 P F ψ g X n θ) (hA5 : A5 P F ψ simLaw X n)
    (hA6 : A6 P ψ simLaw X n θ) (hA7 : A7 P ψ simLaw X n θ)
    (hParams : ∀ k, 2 ≤ B k ∧ 2 ≤ R k ∧ 0 < θ k ∧ θ k ≤ 1)
    (hB : Tendsto (fun k => (B k : ℝ)) atTop atTop)
    (hBR2 : Tendsto (fun k =>
      (B k : ℝ) * (R k : ℝ) ^ 2 / (θ k * nbar (n k)) ^ 2) atTop atTop)
    (hθn : Tendsto (fun k => θ k * nbar (n k)) atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      TendstoInMeasure P (fun k ω =>
        outProb (B := B k) (R := R k) simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (dataSample X (n k) ω)
          {Y | ε < |sigmaHatSVB (θ k) Y / sigmaI ψ P X (n k) - 1|})
        atTop (fun _ => 0) := by
  intro ε hε
  have hP1 := SubsampVB.Consist.proposition_1 P F S ψ g X n hS hData hA1 hA2 hA3
  have hT7 := SubsampVB.Consist.theorem_7 P F S ψ g X n θ hS hData hA1 hA2 hA3 hA4
    (fun k => ⟨(hParams k).2.2.1, (hParams k).2.2.2⟩) hθn
  have hMSE := SubsampVB.Consist.theorem_2_mse_rate P F S ψ g simLaw X n θ B R hS hData
    hOracle hTauFinite hA1 hA2 hA3 hA4 hA5 hA6 hA7 hParams hB hBR2 hθn
  rw [tendstoInMeasure_iff_dist] at hT7 hMSE ⊢
  obtain ⟨hntend, C, hC, hbal⟩ := hA1
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set i0 : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  set c : ℝ := sigma2 F g i0 / (2 * C) with hc_def
  have hc : 0 < c := div_pos (hA3.1 i0).1 (by positivity)
  have hpos : ∀ᶠ k in atTop, ∀ i, (n k i) ≠ 0 := by
    rw [eventually_all]
    intro i
    filter_upwards [(hntend i).eventually_gt_atTop 0] with k hk
    exact_mod_cast hk.ne'
  -- the average sample size is comparable to each `nᵢ`
  have hcomp : ∀ᶠ k in atTop, ∀ i, nbar (n k) ≤ C * n k i ∧ (n k i : ℝ) ≤ C * nbar (n k) := by
    filter_upwards [hbal] with k hk
    intro i
    constructor
    · unfold nbar
      rw [div_le_iff₀ hm]
      calc (∑ j : Fin m, (n k j : ℝ)) ≤ ∑ _j : Fin m, C * n k i :=
            Finset.sum_le_sum (fun j _ => hk j i)
        _ = C * n k i * m := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    · unfold nbar
      rw [mul_div_assoc', le_div_iff₀ hm]
      calc (n k i : ℝ) * m = ∑ _j : Fin m, (n k i : ℝ) := by
            rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ j : Fin m, C * n k j := Finset.sum_le_sum (fun j _ => hk i j)
        _ = C * ∑ j : Fin m, (n k j : ℝ) := by rw [Finset.mul_sum]
  -- lower bound `n̄ σ_I² ≥ c` from Proposition 1
  have hlow : ∀ᶠ k in atTop, 0 < nbar (n k) ∧ c ≤ nbar (n k) * sigmaI ψ P X (n k) := by
    have hev := (Metric.tendsto_nhds.1 hP1) c hc
    filter_upwards [hev, hpos, hcomp] with k hk hk0 hkc
    have hni : (0 : ℝ) < n k i0 := by exact_mod_cast Nat.pos_of_ne_zero (hk0 i0)
    have hnb : 0 < nbar (n k) := by
      have := (hkc i0).2
      have : 0 < C * nbar (n k) := lt_of_lt_of_le hni this
      exact pos_of_mul_pos_right this hC.le
    refine ⟨hnb, ?_⟩
    rw [Real.dist_eq, sub_zero] at hk
    have hS0 : sigma2 F g i0 / (n k i0 : ℝ) ≤ ∑ i : Fin m, sigma2 F g i / (n k i : ℝ) :=
      Finset.single_le_sum (f := fun i => sigma2 F g i / (n k i : ℝ))
        (fun i _ => div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _)) (Finset.mem_univ i0)
    have hσ0 := (hA3.1 i0).1
    have h2c : 2 * c ≤ nbar (n k) * (sigma2 F g i0 / (n k i0 : ℝ)) := by
      have e2 : 2 * c = sigma2 F g i0 / C := by rw [hc_def]; field_simp
      rw [e2, mul_div_assoc', div_le_div_iff₀ hC hni]
      nlinarith [(hkc i0).2, hσ0]
    have h3 := mul_le_mul_of_nonneg_left hS0 hnb.le
    have h4 := (abs_lt.1 hk).1
    nlinarith
  -- subsample sizes are eventually positive
  have hsub : ∀ᶠ k in atTop, ∀ i, subsampleSize (θ k) (n k) i ≠ 0 := by
    filter_upwards [hθn.eventually_ge_atTop C, hcomp] with k hk hkc
    intro i
    unfold subsampleSize
    have hθ := (hParams k).2.2.1
    have h1 : θ k * nbar (n k) ≤ C * (θ k * n k i) := by nlinarith [(hkc i).1]
    have h2 : 1 ≤ θ k * n k i := by nlinarith
    exact (Nat.floor_pos.2 h2).ne'
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  by_cases hγt : γ = ⊤
  · exact Filter.Eventually.of_forall (fun _ => by rw [hγt]; exact le_top)
  set γr := γ.toReal with hγr
  have hγr0 : 0 < γr := ENNReal.toReal_pos hγ.ne' hγt
  obtain ⟨M, hM⟩ := hA7 univ (γr / 3) (by positivity)
  set η : ℝ := δ * ε ^ 2 * c ^ 2 / 8 with hη
  have e1 := (ENNReal.tendsto_nhds_zero.1 (hT7 (ε / 2) (by positivity)))
    (ENNReal.ofReal (γr / 3)) (by simp; positivity)
  have e2 := (ENNReal.tendsto_nhds_zero.1 (hMSE η (by positivity)))
    (ENNReal.ofReal (γr / 3)) (by simp; positivity)
  filter_upwards [e1, e2, hM, hlow, hsub] with k h1 h2 h3 hlowk hsubk
  set x := fun ω => dataSample X (n k) ω
  set Bad1 := {ω | ε / 2 ≤ dist (sigmaSVB ψ (θ k) (dataSample X (n k) ω) /
    sigmaI ψ P X (n k)) 1}
  set Bad2 := {ω | η ≤ dist (nbar (n k) ^ 2 *
        outMSE (B := B k) (R := R k) ψ simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (θ k) (dataSample X (n k) ω)) 0}
  set Bad3 := {ω | (M : ENNReal) <
        bootAvgENN (n := n k) (s := subsampleSize (θ k) (n k))
          (fun I => mu4 ψ simLaw (Fbar univ I (dataSample X (n k) ω)))}
  have hσI : 0 < sigmaI ψ P X (n k) := by
    have := hlowk.2
    have h0 : 0 < nbar (n k) * sigmaI ψ P X (n k) := lt_of_lt_of_le hc this
    exact pos_of_mul_pos_right h0 hlowk.1.le
  have hincl : {ω | δ ≤ dist (outProb (B := B k) (R := R k) simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (dataSample X (n k) ω)
          {Y | ε < |sigmaHatSVB (θ k) Y / sigmaI ψ P X (n k) - 1|}) 0} ⊆
      Bad1 ∪ Bad2 ∪ Bad3 := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨n1, n2⟩, n3⟩ := hnot
    simp only [Bad1, Bad2, Bad3, Set.mem_ofPred_eq, not_le, not_lt] at n1 n2 n3
    simp only [Set.mem_ofPred_eq] at hω
    rw [Real.dist_eq] at n1
    rw [Real.dist_eq, sub_zero] at n2 hω
    -- every resample has finite fourth moment
    have hfin : ∀ J : Resample (n k) (subsampleSize (θ k) (n k)),
        mu4 ψ simLaw (Fbar univ J (dataSample X (n k) ω)) < ⊤ := by
      intro J
      by_contra hJ
      rw [not_lt, top_le_iff] at hJ
      have hsum : (∑ I : Resample (n k) (subsampleSize (θ k) (n k)),
          mu4 ψ simLaw (Fbar univ I (dataSample X (n k) ω))) = ⊤ :=
        ENNReal.sum_eq_top.2 ⟨J, Finset.mem_univ J, hJ⟩
      unfold bootAvgENN at n3
      rw [hsum, ENNReal.mul_top (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))] at n3
      exact ENNReal.coe_ne_top (top_le_iff.1 n3)
    have hprob : ∀ J : Resample (n k) (subsampleSize (θ k) (n k)),
        IsProbabilityMeasure (simLaw (Fbar univ J (dataSample X (n k) ω))) := by
      intro J
      refine (hOracle _ (fun i => ?_)).1
      simp only [Fbar, Finset.mem_univ, if_true]
      exact empirical_isProb _ (hsubk i)
    have hL4 : ∀ J : Resample (n k) (subsampleSize (θ k) (n k)),
        MemLp (fun y : ℝ => y) 4 (simLaw (Fbar univ J (dataSample X (n k) ω))) := by
      intro J
      haveI := hprob J
      exact memLp4_of_mu4 _ (hfin J)
    have hbound := outProb_le (B := B k) (R := R k) simLaw (dataSample X (n k) ω) (θ k)
      (sigmaSVB ψ (θ k) (dataSample X (n k) ω)) (sigmaI ψ P X (n k)) ε hσI hε hprob hL4 n1
    have hMSEdef : ((Fintype.card (Fin (B k) → Resample (n k) (subsampleSize (θ k) (n k))) :
        ℝ)⁻¹ * ∑ I : Fin (B k) → Resample (n k) (subsampleSize (θ k) (n k)),
          ∫ Y, (sigmaHatSVB (θ k) Y - sigmaSVB ψ (θ k) (dataSample X (n k) ω)) ^ 2
            ∂(outputLaw (R := R k) simLaw I (dataSample X (n k) ω))) =
        outMSE (B := B k) (R := R k) ψ simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (θ k) (dataSample X (n k) ω) := rfl
    rw [hMSEdef] at hbound
    set E := outMSE (B := B k) (R := R k) ψ simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (θ k) (dataSample X (n k) ω) with hE
    set σ := sigmaI ψ P X (n k)
    set nb := nbar (n k)
    have hE0 : 0 ≤ E := by
      rw [hE]
      unfold outMSE
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun I _ =>
        integral_nonneg (fun Y => sq_nonneg _)))
    have hop0 : 0 ≤ outProb (B := B k) (R := R k) simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (dataSample X (n k) ω)
          {Y | ε < |sigmaHatSVB (θ k) Y / σ - 1|} := by
      unfold outProb
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun I _ => ENNReal.toReal_nonneg))
    rw [abs_of_nonneg hop0] at hω
    rw [abs_of_nonneg (by positivity)] at n2
    -- E / (εσ/2)² < δ
    have hnbσ : c ≤ nb * σ := hlowk.2
    have hkey : E / ((ε * σ / 2) ^ 2) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      have hc2 : c ^ 2 ≤ (nb * σ) ^ 2 := pow_le_pow_left₀ hc.le hnbσ 2
      have : nb ^ 2 * E * (ε ^ 2 * c ^ 2) ≤ nb ^ 2 * E * (ε ^ 2 * (nb * σ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hc2 (by positivity)
      have hη' : nb ^ 2 * E < δ * ε ^ 2 * c ^ 2 / 8 := n2
      have hnb2 : 0 < nb ^ 2 := by have := hlowk.1; positivity
      -- E * (ε² c²) ≤ ... ; work with nb² E < η
      have h5 : E * (ε ^ 2 * c ^ 2) ≤ E * (ε ^ 2 * (nb * σ) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc2 (by positivity)) hE0
      have h6 : nb ^ 2 * E * (ε ^ 2 * c ^ 2) < δ * ε ^ 2 * c ^ 2 / 8 * (ε ^ 2 * c ^ 2) := by
        apply mul_lt_mul_of_pos_right hη' (by positivity)
      -- goal: E < δ * (εσ/2)²
      have hgoal : E * (ε ^ 2 * c ^ 2) * nb ^ 2 <
          δ * (ε * σ / 2) ^ 2 * (ε ^ 2 * c ^ 2) * nb ^ 2 := by
        have : δ * ε ^ 2 * c ^ 2 / 8 * (ε ^ 2 * c ^ 2) ≤
            δ * (ε * σ / 2) ^ 2 * (ε ^ 2 * c ^ 2) * nb ^ 2 := by
          have hh : (ε ^ 2 * c ^ 2) ≤ ε ^ 2 * (nb * σ) ^ 2 :=
            mul_le_mul_of_nonneg_left hc2 (by positivity)
          have : δ * (ε * σ / 2) ^ 2 * (ε ^ 2 * c ^ 2) * nb ^ 2 =
              δ / 4 * (ε ^ 2 * c ^ 2) * (ε ^ 2 * (nb * σ) ^ 2) := by ring
          rw [this]
          have hpos1 : 0 ≤ δ / 4 * (ε ^ 2 * c ^ 2) := by positivity
          have := mul_le_mul_of_nonneg_left hh hpos1
          nlinarith [sq_nonneg (ε * c)]
        nlinarith
      have hpos2 : 0 < (ε ^ 2 * c ^ 2) * nb ^ 2 := by positivity
      nlinarith
    linarith
  calc P {ω | δ ≤ dist (outProb (B := B k) (R := R k) simLaw (n := n k)
          (s := subsampleSize (θ k) (n k)) (dataSample X (n k) ω)
          {Y | ε < |sigmaHatSVB (θ k) Y / sigmaI ψ P X (n k) - 1|}) 0}
      ≤ P (Bad1 ∪ Bad2 ∪ Bad3) := measure_mono hincl
    _ ≤ P Bad1 + P Bad2 + P Bad3 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (γr / 3) + ENNReal.ofReal (γr / 3) + ENNReal.ofReal (γr / 3) := by
        gcongr
    _ = γ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [show γr / 3 + γr / 3 + γr / 3 = γr by ring, hγr, ENNReal.ofReal_toReal hγt]
