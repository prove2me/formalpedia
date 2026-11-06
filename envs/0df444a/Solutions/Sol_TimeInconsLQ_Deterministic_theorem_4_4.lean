-- Prove2me | solution 1 for TimeInconsLQ.Deterministic.theorem_4_4
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:25:24.178536+00:00
-- url     : https://prove2.me/submissions/bfa7857a-2443-4c92-b5e5-6c83f7d9b93e

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_Deterministic_Model
import Definitions.Def_TimeInconsLQ_Deterministic_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal

open TimeInconsLQ.Deterministic

namespace TILQ2Disproof

open Cardinal in
lemma nnreal_exists_nonmeas : ∃ S : Set ℝ≥0, ¬ MeasurableSet S := by
  by_contra h
  push Not at h
  obtain ⟨b, hbc, hb⟩ := @SecondCountableTopology.is_open_generated_countable ℝ≥0 _ _
  have hborel : (inferInstance : MeasurableSpace ℝ≥0) = MeasurableSpace.generateFrom b := by
    rw [BorelSpace.measurable_eq (α := ℝ≥0)]
    exact borel_eq_generateFrom_of_subbasis hb
  have hcard := @MeasurableSpace.cardinal_measurableSet_le_continuum ℝ≥0 b
    (hbc.le_aleph0.trans aleph0_le_continuum)
  have huniv : {t | @MeasurableSet ℝ≥0 (MeasurableSpace.generateFrom b) t} = Set.univ := by
    ext t; simp only [ Set.mem_univ, iff_true]; rw [← hborel]; exact h t
  rw [huniv, mk_univ, mk_set] at hcard
  have hR : #ℝ ≤ #ℝ≥0 := by
    refine mk_le_of_injective (f := fun x : ℝ => (⟨Real.exp x, (Real.exp_pos x).le⟩ : ℝ≥0)) ?_
    intro x y hxy
    have h2 : Real.exp x = Real.exp y := congrArg Subtype.val hxy
    exact Real.exp_injective h2
  rw [mk_real] at hR
  have : (2 : Cardinal) ^ 𝔠 ≤ 2 ^ #ℝ≥0 := power_le_power_left two_ne_zero hR
  exact absurd (this.trans hcard) (not_le.mpr (cantor 𝔠))

lemma bounded_nonmeas : ∃ S : Set ℝ≥0, ∃ n : ℕ, S ⊆ Set.Iic (n : ℝ≥0) ∧ ¬ MeasurableSet S := by
  obtain ⟨S, hS⟩ := nnreal_exists_nonmeas
  by_contra h
  push Not at h
  apply hS
  have : S = ⋃ n : ℕ, S ∩ Set.Iic (n : ℝ≥0) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iic]
    exact ⟨fun hx => ⟨_, hx, (exists_nat_ge x).choose_spec⟩, fun ⟨_, hx, _⟩ => hx⟩
  rw [this]
  exact MeasurableSet.iUnion fun n => h _ n Set.inter_subset_right

lemma shifted_nonmeas : ∃ S : Set ℝ≥0, ∃ t₀ : ℝ≥0, S ⊆ Set.Iic t₀ ∧ S ⊆ Set.Ici 2 ∧
    ¬ MeasurableSet S := by
  obtain ⟨S, n, hSn, hS⟩ := bounded_nonmeas
  refine ⟨(fun s => s + 2) '' S, n + 2, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have := hSn hs
    simp only [Set.mem_Iic] at this ⊢
    exact add_le_add_left this 2
  · rintro _ ⟨s, hs, rfl⟩
    simp
  · intro hm
    apply hS
    have hmeas : Measurable (fun s : ℝ≥0 => s + 2) := measurable_id.add_const 2
    have := hmeas hm
    rwa [Set.preimage_image_eq S (add_left_injective 2)] at this

noncomputable def cX : Coeffs 1 0 where
  A := fun _ => 0
  B := fun s _ => if s ≤ 1 then 0 else 1
  C := fun _ => 0
  D := fun _ => 0
  b := fun _ => 0
  σ := fun _ => 0
  Q := fun _ => 0
  R := fun _ => 1
  G := 1
  h := 1
  μ₁ := 0
  μ₂ := 0

lemma DtD_cX (s : ℝ≥0) : DtD cX s = 0 := by simp [DtD, cX]
lemma DtC_cX (s : ℝ≥0) : DtC cX s = 0 := by simp [DtC, cX]
lemma Dtσ_cX (s : ℝ≥0) : Dtσ cX s = 0 := by simp [Dtσ, cX]
lemma normC2_cX (s : ℝ≥0) : normC2 cX s = 0 := by simp [normC2, cX]
lemma Gam1_cX (s : ℝ≥0) : Gam1 cX 1 s = 0 := by simp [Gam1, cX]
lemma B_cX {s : ℝ≥0} (hs : s ≤ 1) : cX.B s = 0 := by
  funext i; simp [cX, hs]
lemma Q_cX (s : ℝ≥0) : cX.Q s = 0 := rfl
lemma R_cX (s : ℝ≥0) : cX.R s = 1 := rfl
lemma b_cX (s : ℝ≥0) : cX.b s = 0 := rfl
lemma C_cX (s : ℝ≥0) : cX.C s = 0 := rfl
lemma σ_cX (s : ℝ≥0) : cX.σ s = 0 := rfl
lemma G_cX : cX.G = 1 := rfl
lemma h_cX : cX.h = 1 := rfl
lemma μ₂_cX : cX.μ₂ = 0 := rfl
lemma Kinv_cX (s : ℝ≥0) (m : ℝ) : Kinv cX s m = 1 := by simp [Kinv, DtD_cX, R_cX]
lemma A_cX (s : ℝ≥0) : cX.A s = 0 := rfl

lemma tonn_le {r : ℝ} (h : r ≤ ((1 : ℝ≥0) : ℝ)) : r.toNNReal ≤ 1 := by
  simpa using Real.toNNReal_le_toNNReal h

lemma cX_standing : CoeffsStanding cX 1 where
  A_meas := measurable_const
  A_bdd := ⟨0, fun s _ => by simp [cX]⟩
  B_meas := by
    refine measurable_pi_lambda _ (fun _ => ?_)
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  C_meas := measurable_const
  D_meas := fun _ _ => measurable_const
  b_meas := measurable_const
  σ_meas := measurable_const
  Q_meas := measurable_const
  R_meas := fun _ _ => measurable_const
  B_bdd := ⟨1, ae_of_all _ fun s i => by
    simp only [cX]; split_ifs <;> simp⟩
  C_bdd := ⟨0, ae_of_all _ fun s j => j.elim0⟩
  D_bdd := ⟨0, ae_of_all _ fun s i j => i.elim0⟩
  Q_bdd := ⟨0, ae_of_all _ fun s => by simp [cX]⟩
  R_bdd := ⟨1, ae_of_all _ fun s i j => by
    simp only [cX]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]⟩
  b_L2 := by simp [cX]
  σ_L2 := by simp [cX]
  R_symm := fun _ _ => Matrix.isSymm_one
  Q_nonneg := ae_of_all _ fun _ => le_refl _
  R_psd := ae_of_all _ fun _ => Matrix.PosSemidef.one
  G_nonneg := zero_le_one

lemma cX_case : Case_i cX 1 := by
  refine ⟨⟨1, one_pos, fun s _ => ?_⟩, fun s _ => ?_, ⟨0, le_refl _, fun s hs => ?_⟩⟩
  · simp only [cX, one_smul, sub_self]; exact Matrix.PosSemidef.zero
  · simp only [Q_cX, DtD_cX, normC2_cX, Gam1_cX, DtC_cX, zero_smul, smul_zero, add_zero]
    exact Matrix.PosSemidef.zero
  · rw [B_cX hs, zero_smul]

lemma rhs49M_cX {r : ℝ≥0} (hr : r ≤ 1) : rhs49M cX 1 r 1 1 = 0 := by
  simp [rhs49M, BDC, B_cX hr, DtC_cX, normC2_cX, Gam1_cX, A_cX, Q_cX]
lemma rhs49N_cX {r : ℝ≥0} (hr : r ≤ 1) : rhs49N cX 1 r 1 1 = 0 := by
  simp [rhs49N, BDC, B_cX hr, DtC_cX, Gam1_cX, A_cX]
lemma rhs48_cX (r : ℝ≥0) (φ : ℝ) : rhs48 cX r 1 1 φ = 0 := by
  simp [rhs48, DtC_cX, Dtσ_cX, A_cX, b_cX, C_cX, σ_cX]

lemma cX_pos49 : IsPosSol49 cX 1 (fun _ => 1) (fun _ => 1) := by
  refine ⟨⟨fun s _ => ?_, ?_, ?_, fun s hs => ⟨?_, ?_⟩⟩, fun s _ => ⟨one_pos, one_pos⟩⟩
  · simp [DtD_cX, R_cX]
  · exact (integrableOn_zero).congr_fun
      (fun r hr => (rhs49M_cX (tonn_le hr.2)).symm) measurableSet_Icc
  · exact (integrableOn_zero).congr_fun
      (fun r hr => (rhs49N_cX (tonn_le hr.2)).symm) measurableSet_Icc
  · rw [setIntegral_eq_zero_of_forall_eq_zero (fun r hr => rhs49M_cX (tonn_le hr.2))]
    simp [G_cX]
  · rw [setIntegral_eq_zero_of_forall_eq_zero (fun r hr => rhs49N_cX (tonn_le hr.2))]
    simp [h_cX]

lemma cX_sol48 (S : Set ℝ≥0) (hS : S ⊆ Set.Ici 2) :
    IsSol48 cX 1 (fun _ => 1) (fun _ => 1) (S.indicator fun _ => 1) := by
  refine ⟨(integrableOn_zero).congr_fun (fun r _ => (rhs48_cX _ _).symm) measurableSet_Icc,
    fun s hs => ?_⟩
  rw [setIntegral_eq_zero_of_forall_eq_zero (fun r _ => rhs48_cX _ _)]
  have : s ∉ S := fun h => by
    have := hS h
    simp only [Set.mem_Ici] at this
    exact absurd (this.trans hs) (by norm_num)
  simp [this, μ₂_cX]

lemma brown : Peng1990.SMP.IsStdBrownian (Measure.dirac PUnit.unit : Measure PUnit)
    (fun _ _ => (0 : Fin 0 → ℝ)) where
  meas := fun _ => measurable_const
  brownian := fun j => j.elim0
  indep := iIndepFun.of_subsingleton

end TILQ2Disproof



open TILQ2Disproof in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {l d : ℕ} (c : Coeffs l d) (T : ℝ≥0)
    (hT : 0 < T) (hc : CoeffsStanding c T) (hGh : c.h ≤ c.G) (hh : 0 < c.h)
    (hcase : Case_i c T ∨ Case_ii c T ∨ Case_iii c T),
    HasUniqueSolOn T (IsPosSol49 c T) ∧
    ∀ M N Φ : ℝ≥0 → ℝ, IsPosSol49 c T M N → IsSol48 c T M N Φ →
      ∀ (P : Measure Ω), IsProbabilityMeasure P →
      ∀ (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) (x₀ : Fin 1 → ℝ),
        (∃ X, IsClosedLoop (toData c P W hW T hT x₀)
            (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X) ∧
        ∀ X, IsClosedLoop (toData c P W hW T hT x₀)
            (fun s _ => alpha c T M N s) (fun s _ => beta c M Φ s) X →
          TimeInconsLQ.Sufficient.IsEquilibrium (toData c P W hW T hT x₀)
            (fun s ω => X s ω 0 • alpha c T M N s + beta c M Φ s)) := by
  intro H
  obtain ⟨S, t₀, hSt, hS2, hSm⟩ := shifted_nonmeas
  have key := (H (Ω := PUnit.{1}) cX 1 one_pos cX_standing (le_refl _) one_pos
    (Or.inl cX_case)).2 (fun _ => 1) (fun _ => 1) (S.indicator fun _ => 1) cX_pos49
    (cX_sol48 S hS2) (Measure.dirac PUnit.unit) inferInstance _ brown 0
  have hclosed : IsClosedLoop (toData cX (Measure.dirac (PUnit.unit : PUnit.{1})) _ brown 1 one_pos 0)
      (fun s _ => alpha cX 1 (fun _ => 1) (fun _ => 1) s)
      (fun s _ => beta cX (fun _ => 1) (S.indicator fun _ => 1) s) (fun _ _ => 0) := by
    unfold IsClosedLoop TimeInconsLQ.Sufficient.IsState Peng1990.SMP.SolvesSDE
      Peng1990.SMP.IsItoProcess
    refine ⟨isStronglyProgressive_const _ 0, by simp, fun _ _ _ _ => 0, fun i j => j.elim0,
      fun t ht => ae_of_all _ fun ω => ?_⟩
    have hz : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) t → (fun s : ℝ =>
        (toData cX (Measure.dirac (PUnit.unit : PUnit.{1})) _ brown 1 one_pos 0).A s.toNNReal *ᵥ (0 : Fin 1 → ℝ)
        + ((toData cX (Measure.dirac (PUnit.unit : PUnit.{1})) _ brown 1 one_pos 0).B s.toNNReal ω)ᵀ *ᵥ
          ((0 : Fin 1 → ℝ) 0 • alpha cX 1 (fun _ => 1) (fun _ => 1) s.toNNReal
            + beta cX (fun _ => 1) (S.indicator fun _ => 1) s.toNNReal)
        + (toData cX (Measure.dirac (PUnit.unit : PUnit.{1})) _ brown 1 one_pos 0).b s.toNNReal ω) s = 0 := by
      intro s hs
      have hs1 : s.toNNReal ≤ 1 := tonn_le (hs.2.trans ht)
      simp only [toData, B_cX hs1, b_cX]
      ext i
      simp [Matrix.mulVec, dotProduct]
    refine ⟨(integrableOn_zero).congr_fun (fun r hr => (hz r hr).symm) measurableSet_Icc, ?_⟩
    intro i
    rw [setIntegral_eq_zero_of_forall_eq_zero hz]
    simp [toData]
  have heq := key.2 _ hclosed
  have hprog := heq.1.1 t₀
  have hm := hprog.measurable
  have hg := (measurable_pi_apply 0).comp (hm.comp (measurable_id.prodMk (measurable_const (a := (PUnit.unit : PUnit.{1})))))
  have hval : ∀ x : Set.Iic t₀, ((fun s ω => (fun (_ : ℝ≥0) (_ : PUnit.{1}) => (0 : Fin 1 → ℝ)) s ω 0 •
        alpha cX 1 (fun _ => 1) (fun _ => 1) s +
        TimeInconsLQ.Deterministic.beta cX (fun _ => 1) (S.indicator fun _ => 1) s) x.1 PUnit.unit) 0
        = -(S.indicator (fun _ => (1 : ℝ)) x.1) := by
    intro x
    simp only [TimeInconsLQ.Deterministic.beta, Kinv_cX, Dtσ_cX, smul_zero, add_zero, zero_smul, zero_add, one_mulVec,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x.1 ∈ S
    · have h2 := hS2 hx
      simp only [Set.mem_Ici] at h2
      have hn : ¬ (x.1 ≤ 1) := fun h => absurd (h2.trans h) (by norm_num)
      simp [hx, cX, hn]
    · simp [hx]
  have hpre : (Subtype.val : Set.Iic t₀ → ℝ≥0) ⁻¹' S =
      (fun x : Set.Iic t₀ => ((fun s ω => (fun (_ : ℝ≥0) (_ : PUnit.{1}) => (0 : Fin 1 → ℝ)) s ω 0 •
        alpha cX 1 (fun _ => 1) (fun _ => 1) s +
        TimeInconsLQ.Deterministic.beta cX (fun _ => 1) (S.indicator fun _ => 1) s) x.1 PUnit.unit) 0) ⁻¹' {-1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hval]
    by_cases hx : x.1 ∈ S
    · simp [hx]
    · simp [hx]
  have hmS : MeasurableSet ((Subtype.val : Set.Iic t₀ → ℝ≥0) ⁻¹' S) := by
    rw [hpre]; exact hg (measurableSet_singleton _)
  have := measurableSet_Iic.subtype_image hmS
  rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hSt] at this
  exact hSm this
