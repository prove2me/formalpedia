-- Prove2me | solution 1 for TractableDRO.Unified.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T19:44:03.607243+00:00
-- url     : https://prove2.me/submissions/cc01c448-83ba-4c83-9278-0eec95cc2a03

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix

namespace P59e9

lemma coe_sum {ι : Type} (S : Finset ι) (f : ι → ℝ) :
    ((∑ s ∈ S, f s : ℝ) : EReal) = ∑ s ∈ S, (f s : EReal) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma integrable_dot {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hI : ∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P) (c : ℝ) (r : Fin n → ℝ) :
    Integrable (fun ζ : Fin n → ℝ => c + r ⬝ᵥ ζ) P := by
  have h2 : Integrable (fun ζ : Fin n → ℝ => r ⬝ᵥ ζ) P := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hI i).const_mul (r i)
  exact (integrable_const c).add h2

lemma integral_dot {n : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hI : ∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P) (c : ℝ) (r : Fin n → ℝ) :
    ∫ ζ, (c + r ⬝ᵥ ζ) ∂P = c + r ⬝ᵥ MomentDRO.Conf.meanVec P := by
  have h2 : Integrable (fun ζ : Fin n → ℝ => r ⬝ᵥ ζ) P := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hI i).const_mul (r i)
  rw [integral_add (integrable_const c) h2, integral_const]
  simp only [probReal_univ, one_smul]
  congr 1
  simp only [dotProduct, MomentDRO.Conf.meanVec]
  rw [integral_finsetSum _ fun i _ => (hI i).const_mul (r i)]
  simp_rw [integral_const_mul]

/-! ### Theorem 1 bound -/

lemma bound1 {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (P : Measure (Fin n → ℝ))
    (hP : P ∈ TractableDRO.MeanSupport.family1 V Vhat) (r0 : ℝ) (r : Fin n → ℝ) :
    ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal) ≤
      TractableDRO.Unified.pi1 V Vhat r0 r := by
  obtain ⟨hprob, hI, hm, hV⟩ := hP
  have := hprob
  unfold TractableDRO.Unified.pi1
  refine le_iInf fun s => ?_
  have hA : ((s ⬝ᵥ MomentDRO.Conf.meanVec P : ℝ) : EReal) ≤
      ⨆ ζh ∈ Vhat, ((s ⬝ᵥ ζh : ℝ) : EReal) :=
    le_iSup₂_of_le (MomentDRO.Conf.meanVec P) hm le_rfl
  by_cases htop : (⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal)) = ⊤
  · rw [htop, EReal.add_top_of_ne_bot]
    · exact le_top
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hA
  · have hVne : V.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne] at hV
      have h0 : P {ζ | ¬ ζ ∈ (∅ : Set (Fin n → ℝ))} = 0 := ae_iff.1 hV
      simp only [Set.mem_empty_iff_false, not_false_eq_true, Set.ofPred_true, measure_univ] at h0
      exact one_ne_zero h0
    obtain ⟨ζ0, hζ0⟩ := hVne
    have hbot : (⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal)) ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_iSup₂_of_le ζ0 hζ0 le_rfl)
    obtain ⟨b, hMb⟩ : ∃ b : ℝ,
        (⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal)) = (b : EReal) :=
      ⟨_, (EReal.coe_toReal htop hbot).symm⟩
    have hle : ∀ ζ ∈ V, max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) ≤ b := fun ζ hζ => by
      have : ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal) ≤
          ⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal) :=
        le_iSup₂_of_le ζ hζ le_rfl
      rw [hMb] at this
      exact EReal.coe_le_coe_iff.1 this
    have hE : TractableDRO.MeanSupport.expPos P r0 r ≤
        s ⬝ᵥ MomentDRO.Conf.meanVec P + b := by
      unfold TractableDRO.MeanSupport.expPos
      have h1 := (integrable_dot P hI r0 r).pos_part
      have h2 := integrable_dot P hI b s
      calc ∫ ζ, max (r0 + r ⬝ᵥ ζ) 0 ∂P ≤ ∫ ζ, (b + s ⬝ᵥ ζ) ∂P := by
            refine integral_mono_ae h1 h2 ?_
            filter_upwards [hV] with ζ hζ
            have hb := hle ζ hζ
            have e : max (r0 + r ⬝ᵥ ζ) 0 =
                s ⬝ᵥ ζ + max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) := by
              rw [← max_add_add_left]; congr 1 <;> ring
            rw [e]; linarith
        _ = s ⬝ᵥ MomentDRO.Conf.meanVec P + b := by rw [integral_dot P hI]; ring
    rw [hMb]
    calc ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal)
        ≤ ((s ⬝ᵥ MomentDRO.Conf.meanVec P + b : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hE
      _ = ((s ⬝ᵥ MomentDRO.Conf.meanVec P : ℝ) : EReal) + (b : EReal) := EReal.coe_add _ _
      _ ≤ _ := add_le_add hA le_rfl

/-! ### Theorem 2 bound (from the MeanCov theorem 2 proof) -/

lemma max_zero_eq (t : ℝ) : max t 0 = (t + |t|) / 2 := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

lemma upper {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (P : Measure (Fin n → ℝ))
    (hP : P ∈ TractableDRO.MeanCov.family2 F Sig Vhat) (r0 : ℝ) (y : Fin N → ℝ) :
    TractableDRO.MeanSupport.expPos P r0 (Fᵀ *ᵥ y) ≤
      (r0 + (Fᵀ *ᵥ y) ⬝ᵥ MomentDRO.Conf.meanVec P) / 2 +
        Real.sqrt ((r0 + (Fᵀ *ᵥ y) ⬝ᵥ MomentDRO.Conf.meanVec P) ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2 := by
  obtain ⟨⟨hprob, hL2⟩, -, hcov⟩ := hP
  have := hprob
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = MomentDRO.Conf.meanVec P := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Fᵀ *ᵥ y := ⟨_, rfl⟩
  rw [← hμ, ← hr]
  obtain ⟨m, hm⟩ : ∃ m, m = r0 + r ⬝ᵥ μ := ⟨_, rfl⟩
  rw [← hm]
  have hEi : ∀ i, ∫ ζ, ζ i ∂P = μ i := fun i => by rw [hμ]; rfl
  have hI : ∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P := fun i => (hL2 i).integrable one_le_two
  have hLi : ∀ i, MemLp (fun ζ : Fin n → ℝ => ζ i - μ i) 2 P := fun i => (hL2 i).sub (memLp_const _)
  have hDL : MemLp (fun ζ : Fin n → ℝ => ∑ i, r i * (ζ i - μ i)) 2 P :=
    memLp_finsetSum _ (fun i _ => (hLi i).const_mul (r i))
  have hT : ∀ ζ : Fin n → ℝ, r0 + r ⬝ᵥ ζ = m + ∑ i, r i * (ζ i - μ i) := by
    intro ζ
    simp only [hm, dotProduct, mul_sub, Finset.sum_sub_distrib]; ring
  have hD0 : ∫ ζ, ∑ i, r i * (ζ i - μ i) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => ((hLi i).integrable one_le_two).const_mul (r i))]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, integral_sub (hI i) (integrable_const _), hEi, integral_const]
    simp
  have hD2 : ∫ ζ, (∑ i, r i * (ζ i - μ i)) ^ 2 ∂P = y ⬝ᵥ Sig *ᵥ y := by
    have hpt : ∀ ζ : Fin n → ℝ, (∑ i, r i * (ζ i - μ i)) ^ 2 =
        ∑ i, ∑ j, r i * r j * ((ζ i - μ i) * (ζ j - μ j)) := by
      intro ζ; rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    have hint : ∀ i j, Integrable (fun ζ : Fin n → ℝ => (ζ i - μ i) * (ζ j - μ j)) P :=
      fun i j => (hLi i).integrable_mul (hLi j)
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hint i j).const_mul _))]
    simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).const_mul _), integral_const_mul]
    have hq : y ⬝ᵥ (F * MomentDRO.Conf.covMat P * Fᵀ) *ᵥ y =
        r ⬝ᵥ MomentDRO.Conf.covMat P *ᵥ r := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, ← hr]
    rw [← hcov, hq]
    simp only [dotProduct, Matrix.mulVec, MomentDRO.Conf.covMat, MomentDRO.Conf.secondMomentAbout,
      ← hμ, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hT2 : MemLp (fun ζ : Fin n → ℝ => r0 + r ⬝ᵥ ζ) 2 P := by
    have : (fun ζ : Fin n → ℝ => r0 + r ⬝ᵥ ζ) = fun ζ => m + ∑ i, r i * (ζ i - μ i) := funext hT
    rw [this]; exact (memLp_const m).add hDL
  have hET : ∫ ζ, (r0 + r ⬝ᵥ ζ) ∂P = m := by
    simp_rw [hT]
    rw [integral_add (integrable_const _) (hDL.integrable one_le_two), hD0, integral_const]
    simp
  have hET2 : ∫ ζ, (r0 + r ⬝ᵥ ζ) ^ 2 ∂P = m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    have hpt : ∀ ζ : Fin n → ℝ, (r0 + r ⬝ᵥ ζ) ^ 2 =
        m ^ 2 + 2 * m * (∑ i, r i * (ζ i - μ i)) + (∑ i, r i * (ζ i - μ i)) ^ 2 := by
      intro ζ; rw [hT]; ring
    simp_rw [hpt]
    have hDi := hDL.integrable one_le_two
    rw [integral_add (f := fun ζ : Fin n → ℝ => m ^ 2 + 2 * m * ∑ i, r i * (ζ i - μ i))
      (g := fun ζ : Fin n → ℝ => (∑ i, r i * (ζ i - μ i)) ^ 2)
      ((integrable_const _).add (hDi.const_mul _)) hDL.integrable_sq,
      integral_add (integrable_const _) (hDi.const_mul _), integral_const_mul, hD0, hD2,
      integral_const]
    simp
  have habs : MemLp (fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) 2 P := hT2.abs
  have hvar := ProbabilityTheory.variance_nonneg (fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) P
  rw [ProbabilityTheory.variance_eq_sub habs] at hvar
  have hsq : ∫ x, ((fun ζ : Fin n → ℝ => |r0 + r ⬝ᵥ ζ|) ^ 2) x ∂P = m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    simp only [Pi.pow_apply, sq_abs]; exact hET2
  rw [hsq] at hvar
  have hnn : 0 ≤ m ^ 2 + y ⬝ᵥ Sig *ᵥ y := by
    rw [← hET2]; exact integral_nonneg fun _ => sq_nonneg _
  have hAbs : ∫ ζ, |r0 + r ⬝ᵥ ζ| ∂P ≤ Real.sqrt (m ^ 2 + y ⬝ᵥ Sig *ᵥ y) := by
    rw [Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _) hnn]
    linarith
  unfold TractableDRO.MeanSupport.expPos
  simp_rw [max_zero_eq]
  rw [integral_div, integral_add (hT2.integrable one_le_two) (habs.integrable one_le_two), hET]
  linarith

lemma bound2 {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (P : Measure (Fin n → ℝ))
    (hP : P ∈ TractableDRO.MeanCov.family2 F Sig Vhat) (r0 : ℝ) (r : Fin n → ℝ) :
    ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal) ≤
      TractableDRO.MeanCov.pi2 F Sig Vhat r0 r := by
  unfold TractableDRO.MeanCov.pi2
  refine le_iInf₂ fun y hy => ?_
  have hy' : Fᵀ *ᵥ y = r := hy
  refine le_iSup₂_of_le (MomentDRO.Conf.meanVec P) hP.2.1 (EReal.coe_le_coe_iff.2 ?_)
  rw [← hy']
  exact upper F Sig Vhat P hP r0 y

/-! ### Theorem 3 bound -/

lemma max_le_exp (t lam : ℝ) (hl : 0 < lam) :
    max t 0 ≤ lam / Real.exp 1 * Real.exp (t / lam) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h0 : 0 ≤ lam / Real.exp 1 * Real.exp (t / lam) := by positivity
  refine max_le ?_ h0
  have h1 := Real.add_one_le_exp (t / lam - 1)
  rw [Real.exp_sub] at h1
  have h2 : t / lam ≤ Real.exp (t / lam) / Real.exp 1 := by linarith
  calc t = lam * (t / lam) := by field_simp
    _ ≤ lam * (Real.exp (t / lam) / Real.exp 1) := mul_le_mul_of_nonneg_left h2 hl.le
    _ = lam / Real.exp 1 * Real.exp (t / lam) := by ring

lemma mgf_fwd (Q : Measure ℝ) [IsProbabilityMeasure Q] (σ : ℝ)
    (hf : DataDrivenRO.FwdBwd.FwdDevLe Q σ) (θ : ℝ) (hθ : 0 < θ)
    (hint : Integrable (fun t => Real.exp (θ * t)) Q) :
    ∫ t, Real.exp (θ * t) ∂Q ≤ Real.exp (θ * (∫ t, t ∂Q) + θ ^ 2 * σ ^ 2 / 2) := by
  have hpos : 0 < ∫ t, Real.exp (θ * t) ∂Q := integral_exp_pos hint
  have h := hf θ hθ
  set L := Real.log (∫ t, Real.exp (θ * t) ∂Q)
  set μ := ∫ t, t ∂Q
  have key : θ ^ 2 / 2 * (-2 * μ / θ + 2 / θ ^ 2 * L) = -(μ * θ) + L := by
    field_simp; try ring
  have h2 : θ ^ 2 / 2 * (-2 * μ / θ + 2 / θ ^ 2 * L) ≤ θ ^ 2 / 2 * σ ^ 2 :=
    mul_le_mul_of_nonneg_left h (by positivity)
  rw [key] at h2
  rw [← Real.log_le_iff_le_exp hpos]
  linarith

lemma mgf_bwd (Q : Measure ℝ) [IsProbabilityMeasure Q] (σ : ℝ)
    (hb : DataDrivenRO.FwdBwd.BwdDevLe Q σ) (θ : ℝ) (hθ : θ < 0)
    (hint : Integrable (fun t => Real.exp (θ * t)) Q) :
    ∫ t, Real.exp (θ * t) ∂Q ≤ Real.exp (θ * (∫ t, t ∂Q) + θ ^ 2 * σ ^ 2 / 2) := by
  have hpos : 0 < ∫ t, Real.exp (θ * t) ∂Q := integral_exp_pos hint
  have h := hb (-θ) (by linarith)
  simp only [neg_neg] at h
  set L := Real.log (∫ t, Real.exp (θ * t) ∂Q)
  set μ := ∫ t, t ∂Q
  have key : θ ^ 2 / 2 * (2 * μ / -θ + 2 / (-θ) ^ 2 * L) = -(μ * θ) + L := by
    have : θ ≠ 0 := hθ.ne
    field_simp; try ring
  have h2 : θ ^ 2 / 2 * (2 * μ / -θ + 2 / (-θ) ^ 2 * L) ≤ θ ^ 2 / 2 * σ ^ 2 :=
    mul_le_mul_of_nonneg_left h (by positivity)
  rw [key] at h2
  rw [← Real.log_le_iff_le_exp hpos]
  linarith

lemma mgf_coord (Q : Measure ℝ) [IsProbabilityMeasure Q] (σf σb : ℝ) (hσf : 0 ≤ σf)
    (hσb : 0 ≤ σb) (hf : DataDrivenRO.FwdBwd.FwdDevLe Q σf)
    (hb : DataDrivenRO.FwdBwd.BwdDevLe Q σb)
    (hint : ∀ θ : ℝ, Integrable (fun t => Real.exp (θ * t)) Q) (a lam : ℝ) (hl : 0 < lam) :
    ∫ t, Real.exp (a / lam * t) ∂Q ≤
      Real.exp (a / lam * (∫ t, t ∂Q) + max (a * σf) (-(a * σb)) ^ 2 / (2 * lam ^ 2)) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hθ : a / lam < 0 := div_neg_of_neg_of_pos ha hl
    refine (mgf_bwd Q σb hb _ hθ (hint _)).trans (le_of_eq ?_)
    have hm : max (a * σf) (-(a * σb)) = -(a * σb) := by
      apply max_eq_right; nlinarith
    rw [hm]; congr 1; field_simp; try ring
  · subst ha; simp
  · have hθ : 0 < a / lam := div_pos ha hl
    refine (mgf_fwd Q σf hf _ hθ (hint _)).trans (le_of_eq ?_)
    have hm : max (a * σf) (-(a * σb)) = a * σf := by
      apply max_eq_left; nlinarith
    rw [hm]; congr 1; field_simp; try ring

lemma bound_psi {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ)
    (Vhat : Set (Fin n → ℝ)) (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ)
    (hσf : 0 ≤ σf) (hσb : 0 ≤ σb) (P : Measure (Fin n → ℝ))
    (hP : P ∈ TractableDRO.Unified.family3 Fσ gσ Vhat σf σb)
    (hzh : Fσ *ᵥ MomentDRO.Conf.meanVec P + gσ ∈ Wσhat) (a0 : ℝ) (a : Fin Nσ → ℝ) :
    ((∫ ζ, max (a0 + a ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P : ℝ) : EReal) ≤
      TractableDRO.Unified.psi Wσhat σf σb a0 a := by
  obtain ⟨hprob, hI, hm, hind, hexp, hfwd, hbwd⟩ := hP
  have := hprob
  unfold TractableDRO.Unified.psi
  refine le_iInf₂ fun lam hlam => le_iSup₂_of_le _ hzh (EReal.coe_le_coe_iff.2 ?_)
  set zh := Fσ *ᵥ MomentDRO.Conf.meanVec P + gσ with hzh_def
  have hzm : ∀ j, Measurable (fun ζ : Fin n → ℝ => TractableDRO.Unified.zσ Fσ gσ ζ j) := by
    intro j
    simp only [TractableDRO.Unified.zσ, Pi.add_apply, Matrix.mulVec, dotProduct]
    fun_prop
  have hzI : ∀ j, ∫ ζ, TractableDRO.Unified.zσ Fσ gσ ζ j ∂P = zh j := by
    intro j
    have : (fun ζ : Fin n → ℝ => TractableDRO.Unified.zσ Fσ gσ ζ j) =
        fun ζ => gσ j + (fun k => Fσ j k) ⬝ᵥ ζ := by
      funext ζ; simp only [TractableDRO.Unified.zσ, Pi.add_apply, Matrix.mulVec]; ring
    rw [this, integral_dot P hI]
    simp only [hzh_def, Pi.add_apply, Matrix.mulVec]; ring
  -- the summands
  set X : Fin Nσ → (Fin n → ℝ) → ℝ :=
    fun j ζ => a j * TractableDRO.Unified.zσ Fσ gσ ζ j with hX
  have hXm : ∀ j, Measurable (X j) := fun j => (hzm j).const_mul (a j)
  have hXind : iIndepFun X P :=
    hind.comp (fun j t => a j * t) (fun j => measurable_const.mul measurable_id)
  have hXint : ∀ j ∈ (Finset.univ : Finset (Fin Nσ)),
      Integrable (fun ζ => Real.exp (1 / lam * X j ζ)) P := by
    intro j _
    refine (hexp j (1 / lam * a j)).congr (ae_of_all _ fun ζ => ?_)
    simp only [hX]; ring_nf
  have hGint := hXind.integrable_exp_mul_sum hXm hXint
  have hfun : (fun ζ => lam / Real.exp 1 *
      Real.exp ((a0 + a ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) / lam)) =
      fun ζ => (lam / Real.exp 1 * Real.exp (a0 / lam)) *
        Real.exp (1 / lam * (∑ j ∈ Finset.univ, X j) ζ) := by
    funext ζ
    rw [mul_assoc, ← Real.exp_add, Finset.sum_apply]
    congr 2
    simp only [hX, dotProduct]
    rw [Finset.mul_sum, add_div, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hRint : Integrable (fun ζ => lam / Real.exp 1 *
      Real.exp ((a0 + a ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) / lam)) P := by
    rw [hfun]; exact hGint.const_mul _
  -- per-coordinate bound
  have hcoord : ∀ j, mgf (X j) P (1 / lam) ≤ Real.exp (a j / lam * zh j +
      TractableDRO.Unified.uvec σf σb a j ^ 2 / (2 * lam ^ 2)) := by
    intro j
    have : IsProbabilityMeasure (P.map (fun ζ => TractableDRO.Unified.zσ Fσ gσ ζ j)) :=
      Measure.isProbabilityMeasure_map (hzm j).aemeasurable
    have hQint : ∀ θ : ℝ, Integrable (fun t => Real.exp (θ * t))
        (P.map (fun ζ => TractableDRO.Unified.zσ Fσ gσ ζ j)) := fun θ =>
      (integrable_map_measure (by fun_prop) (hzm j).aemeasurable).2 (hexp j θ)
    have hmean : ∫ t, t ∂(P.map (fun ζ => TractableDRO.Unified.zσ Fσ gσ ζ j)) = zh j := by
      exact (integral_map (f := fun t : ℝ => t) (hzm j).aemeasurable (by fun_prop)).trans (hzI j)
    have h := mgf_coord _ (σf j) (σb j) (hσf j) (hσb j) (hfwd j) (hbwd j) hQint (a j) lam hlam
    rw [hmean, integral_map (hzm j).aemeasurable (by fun_prop)] at h
    refine le_of_eq_of_le ?_ h
    unfold mgf
    congr 1; funext ζ; congr 1; simp only [hX]; ring
  calc ∫ ζ, max (a0 + a ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P
      ≤ ∫ ζ, lam / Real.exp 1 *
          Real.exp ((a0 + a ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) / lam) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ζ => le_max_right _ _) hRint
          (ae_of_all _ fun ζ => max_le_exp _ _ hlam)
    _ = (lam / Real.exp 1 * Real.exp (a0 / lam)) * mgf (∑ j ∈ Finset.univ, X j) P (1 / lam) := by
        rw [hfun, integral_const_mul]; rfl
    _ = (lam / Real.exp 1 * Real.exp (a0 / lam)) * ∏ j ∈ Finset.univ, mgf (X j) P (1 / lam) := by
        rw [hXind.mgf_sum hXm]
    _ ≤ (lam / Real.exp 1 * Real.exp (a0 / lam)) * ∏ j ∈ Finset.univ, Real.exp (a j / lam * zh j +
          TractableDRO.Unified.uvec σf σb a j ^ 2 / (2 * lam ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.prod_le_prod (fun j _ => mgf_nonneg) (fun j _ => hcoord j)
    _ = lam / Real.exp 1 * Real.exp ((a0 + a ⬝ᵥ zh) / lam +
          (∑ j, TractableDRO.Unified.uvec σf σb a j ^ 2) / (2 * lam ^ 2)) := by
        rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
        congr 2
        have hs : ∑ j, a j / lam * zh j = (∑ j, a j * zh j) / lam := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [Finset.sum_add_distrib, ← Finset.sum_div, hs, dotProduct]; ring

lemma pos_split (y w : ℝ) : max y 0 ≤ (y - w) + max (w - y) 0 + max w 0 := by
  have := le_max_left (w - y) 0
  have := le_max_right (w - y) 0
  have := le_max_left w 0
  have := le_max_right w 0
  exact max_le (by linarith) (by linarith)

lemma bound3 {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ)
    (Vhat : Set (Fin n → ℝ)) (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ)
    (hσf : 0 ≤ σf) (hσb : 0 ≤ σb) (hW : ∀ ζh ∈ Vhat, Fσ *ᵥ ζh + gσ ∈ Wσhat)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ TractableDRO.Unified.family3 Fσ gσ Vhat σf σb)
    (r0 : ℝ) (r : Fin n → ℝ) :
    ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal) ≤
      TractableDRO.Unified.pi3 Fσ gσ Vhat Wσhat σf σb r0 r := by
  have hP' := hP
  obtain ⟨hprob, hI, hm, -, -, -, -⟩ := hP'
  have := hprob
  have hzh := hW _ hm
  unfold TractableDRO.Unified.pi3
  refine le_iInf fun s0 => le_iInf fun s => le_iInf fun x0 => le_iInf fun x =>
    le_iInf fun hx0 => le_iInf fun hx => ?_
  have hB : (((r - Fσᵀ *ᵥ s) ⬝ᵥ MomentDRO.Conf.meanVec P : ℝ) : EReal) ≤
      ⨆ ζh ∈ Vhat, (((r - Fσᵀ *ᵥ s) ⬝ᵥ ζh : ℝ) : EReal) :=
    le_iSup₂_of_le _ hm le_rfl
  have hC := bound_psi Fσ gσ Vhat Wσhat σf σb hσf hσb P hP hzh (s0 - x0) (s - x)
  have hD := bound_psi Fσ gσ Vhat Wσhat σf σb hσf hσb P hP hzh s0 s
  have hlin : ∀ (c0 : ℝ) (c : Fin Nσ → ℝ), (fun ζ => c0 + c ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) =
      fun ζ => (c0 + c ⬝ᵥ gσ) + (Fσᵀ *ᵥ c) ⬝ᵥ ζ := by
    intro c0 c; funext ζ
    simp only [TractableDRO.Unified.zσ, dotProduct_add, Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
    ring
  have hlinI : ∀ (c0 : ℝ) (c : Fin Nσ → ℝ),
      Integrable (fun ζ => c0 + c ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) P := by
    intro c0 c; rw [hlin]; exact integrable_dot P hI _ _
  have hxz : ∀ ζ, x ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ = r ⬝ᵥ ζ + (r0 - x0) := by
    intro ζ
    simp only [TractableDRO.Unified.zσ, dotProduct_add, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hx]
    linarith
  have hpt : ∀ ζ, max (r0 + r ⬝ᵥ ζ) 0 ≤
      ((r0 + r ⬝ᵥ ζ) - (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ)) +
      max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 +
      max (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 := by
    intro ζ
    have e : (s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ =
        (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) - (r0 + r ⬝ᵥ ζ) := by
      rw [sub_dotProduct, hxz]; ring
    rw [e]; exact pos_split _ _
  have hreal : TractableDRO.MeanSupport.expPos P r0 r ≤
      (r0 - s0 - s ⬝ᵥ gσ) + (r - Fσᵀ *ᵥ s) ⬝ᵥ MomentDRO.Conf.meanVec P +
      (∫ ζ, max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P) +
      (∫ ζ, max (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P) := by
    unfold TractableDRO.MeanSupport.expPos
    have i1 := integrable_dot P hI r0 r
    have i2 := hlinI s0 s
    have i3 := (hlinI (s0 - x0) (s - x)).pos_part
    have i4 := (hlinI s0 s).pos_part
    have i12 : Integrable (fun ζ => (r0 + r ⬝ᵥ ζ) -
        (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ)) P := i1.sub i2
    have i123 : Integrable (fun ζ => ((r0 + r ⬝ᵥ ζ) -
        (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ)) +
        max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0) P := i12.add i3
    have i1234 : Integrable (fun ζ => ((r0 + r ⬝ᵥ ζ) -
        (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ)) +
        max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 +
        max (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0) P := i123.add i4
    refine (integral_mono i1.pos_part i1234 hpt).trans (le_of_eq ?_)
    rw [integral_add i123 i4, integral_add i12 i3, integral_sub i1 i2,
      integral_dot P hI, hlin, integral_dot P hI, sub_dotProduct, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec]
    ring
  calc ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal)
      ≤ (((r0 - s0 - s ⬝ᵥ gσ) + (r - Fσᵀ *ᵥ s) ⬝ᵥ MomentDRO.Conf.meanVec P +
      (∫ ζ, max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P) +
      (∫ ζ, max (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 hreal
    _ = ((r0 - s0 - s ⬝ᵥ gσ : ℝ) : EReal) +
          (((r - Fσᵀ *ᵥ s) ⬝ᵥ MomentDRO.Conf.meanVec P : ℝ) : EReal) +
          ((∫ ζ, max ((s0 - x0) + (s - x) ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P : ℝ) : EReal) +
          ((∫ ζ, max (s0 + s ⬝ᵥ TractableDRO.Unified.zσ Fσ gσ ζ) 0 ∂P : ℝ) : EReal) := by
        simp only [EReal.coe_add]
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hB) hC) hD

/-! ### Assembly -/

lemma prob_of_mem {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ) (s : Fin 3)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ TractableDRO.Unified.familyOf D s) :
    IsProbabilityMeasure P ∧ ∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P := by
  fin_cases s
  · exact ⟨hP.1, hP.2.1⟩
  · have h1 := hP.1.1
    exact ⟨h1, fun i => (hP.1.2 i).integrable one_le_two⟩
  · exact ⟨hP.1, hP.2.1⟩

lemma bound_of_mem {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ) (hσf : 0 ≤ D.σf)
    (hσb : 0 ≤ D.σb) (hW : ∀ ζh ∈ D.Vhat, D.Fσ *ᵥ ζh + D.gσ ∈ D.Wσhat) (s : Fin 3)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ TractableDRO.Unified.familyOf D s) (r0 : ℝ)
    (r : Fin n → ℝ) :
    ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal) ≤
      TractableDRO.Unified.piOf D s r0 r := by
  fin_cases s
  · exact bound1 D.V D.Vhat P hP r0 r
  · exact bound2 D.F D.Sig D.Vhat P hP r0 r
  · exact bound3 D.Fσ D.gσ D.Vhat D.Wσhat D.σf D.σb hσf hσb hW P hP r0 r

lemma part1 {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ) (S : Finset (Fin 3))
    (hσf : 0 ≤ D.σf) (hσb : 0 ≤ D.σb) (hW : ∀ ζh ∈ D.Vhat, D.Fσ *ᵥ ζh + D.gσ ∈ D.Wσhat)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (TractableDRO.Unified.familyU D S) r0 r ≤
      TractableDRO.Unified.piU D S r0 r := by
  unfold TractableDRO.MeanSupport.worstCase TractableDRO.Unified.piU
  refine iSup₂_le fun P hP => le_iInf fun r0s => le_iInf fun rs => le_iInf fun h0 =>
    le_iInf fun h1 => ?_
  have hPs : ∀ s ∈ S, P ∈ TractableDRO.Unified.familyOf D s := by
    intro s hs
    simp only [TractableDRO.Unified.familyU, Set.mem_iInter] at hP
    exact hP s hs
  have hreal : TractableDRO.MeanSupport.expPos P r0 r ≤
      ∑ s ∈ S, TractableDRO.MeanSupport.expPos P (r0s s) (rs s) := by
    unfold TractableDRO.MeanSupport.expPos
    have hint : ∀ s ∈ S, Integrable (fun ζ : Fin n → ℝ => max (r0s s + rs s ⬝ᵥ ζ) 0) P := by
      intro s hs
      obtain ⟨hpr, hI⟩ := prob_of_mem D s P (hPs s hs)
      have := hpr
      exact (integrable_dot P hI _ _).pos_part
    rw [← integral_finsetSum _ hint]
    refine integral_mono_of_nonneg (ae_of_all _ fun ζ => le_max_right _ _)
      (integrable_finsetSum _ hint) (ae_of_all _ fun ζ => ?_)
    have e : r0 + r ⬝ᵥ ζ = ∑ s ∈ S, (r0s s + rs s ⬝ᵥ ζ) := by
      rw [Finset.sum_add_distrib, h0, h1, sum_dotProduct]
    show max (r0 + r ⬝ᵥ ζ) 0 ≤ ∑ s ∈ S, max (r0s s + rs s ⬝ᵥ ζ) 0
    rw [e]
    exact max_le (Finset.sum_le_sum fun s _ => le_max_left _ _)
      (Finset.sum_nonneg fun s _ => le_max_right _ _)
  calc ((TractableDRO.MeanSupport.expPos P r0 r : ℝ) : EReal)
      ≤ ((∑ s ∈ S, TractableDRO.MeanSupport.expPos P (r0s s) (rs s) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 hreal
    _ = ∑ s ∈ S, ((TractableDRO.MeanSupport.expPos P (r0s s) (rs s) : ℝ) : EReal) := coe_sum S _
    _ ≤ _ := Finset.sum_le_sum fun s hs => bound_of_mem D hσf hσb hW s P (hPs s hs) _ _

lemma psi_zero_le {Nσ : ℕ} (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ) :
    TractableDRO.Unified.psi Wσhat σf σb 0 0 ≤ 0 := by
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  have hz' : (0 : ℝ) < z := EReal.coe_lt_coe_iff.1 (by simpa using hz)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  unfold TractableDRO.Unified.psi
  refine (iInf₂_le (z * Real.exp 1) (by positivity)).trans (iSup₂_le fun zh _ => ?_)
  refine EReal.coe_le_coe_iff.2 (le_of_eq ?_)
  simp [TractableDRO.Unified.uvec]
  try field_simp

lemma piOf_zero_le {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ) (s : Fin 3) :
    TractableDRO.Unified.piOf D s 0 0 ≤ 0 := by
  fin_cases s
  · show TractableDRO.Unified.pi1 D.V D.Vhat 0 0 ≤ 0
    unfold TractableDRO.Unified.pi1
    refine (iInf_le _ 0).trans ?_
    calc _ ≤ (0 : EReal) + 0 :=
          add_le_add (iSup₂_le fun _ _ => by simp) (iSup₂_le fun _ _ => by simp)
      _ = 0 := add_zero 0
  · show TractableDRO.MeanCov.pi2 D.F D.Sig D.Vhat 0 0 ≤ 0
    unfold TractableDRO.MeanCov.pi2
    exact (iInf₂_le 0 (by simp)).trans (iSup₂_le fun _ _ => by simp)
  · show TractableDRO.Unified.pi3 D.Fσ D.gσ D.Vhat D.Wσhat D.σf D.σb 0 0 ≤ 0
    unfold TractableDRO.Unified.pi3
    refine (iInf_le _ 0).trans ((iInf_le _ 0).trans ((iInf_le _ 0).trans ((iInf_le _ 0).trans
      ((iInf_le _ (by simp)).trans ((iInf_le _ (by simp)).trans ?_)))))
    rw [sub_self, sub_self]
    calc _ ≤ (0 : EReal) + 0 + 0 + 0 :=
          add_le_add (add_le_add (add_le_add (by simp) (iSup₂_le fun _ _ => by simp))
            (psi_zero_le _ _ _)) (psi_zero_le _ _ _)
      _ = 0 := by simp

lemma part2 {n N Nσ : ℕ} (D : TractableDRO.Unified.Data n N Nσ) (S : Finset (Fin 3))
    (r0 : ℝ) (r : Fin n → ℝ) (s : Fin 3) (hs : s ∈ S) :
    TractableDRO.Unified.piU D S r0 r ≤ TractableDRO.Unified.piOf D s r0 r := by
  classical
  unfold TractableDRO.Unified.piU
  refine (iInf_le _ (fun t => if t = s then r0 else 0)).trans
    ((iInf_le _ (fun t => if t = s then r else 0)).trans
    ((iInf_le _ ?_).trans ((iInf_le _ ?_).trans ?_)))
  · rw [Finset.sum_ite_eq', if_pos hs]
  · rw [Finset.sum_ite_eq', if_pos hs]
  · rw [← Finset.add_sum_erase S _ hs]
    simp only [if_true]
    calc _ ≤ TractableDRO.Unified.piOf D s r0 r + 0 := by
          refine add_le_add le_rfl (Finset.sum_nonpos fun t ht => ?_)
          rw [if_neg (Finset.ne_of_mem_erase ht), if_neg (Finset.ne_of_mem_erase ht)]
          exact piOf_zero_le D t
      _ = _ := add_zero _

end P59e9

open MeasureTheory ProbabilityTheory Matrix TractableDRO.Unified in
theorem solution {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3))
    (hσf : 0 ≤ D.σf) (hσb : 0 ≤ D.σb) (hW : ∀ ζh ∈ D.Vhat, D.Fσ *ᵥ ζh + D.gσ ∈ D.Wσhat)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (familyU D S) r0 r ≤ piU D S r0 r ∧ ∀ s ∈ S, piU D S r0 r ≤ piOf D s r0 r := by
  exact ⟨P59e9.part1 D S hσf hσb hW r0 r, fun s hs => P59e9.part2 D S r0 r s hs⟩
