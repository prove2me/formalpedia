-- Prove2me | solution 1 for RiskFunctionals.Duality.fenchel_moreau
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T04:01:32.178449+00:00
-- url     : https://prove2.me/submissions/eb4eefd0-199a-4a0a-a652-5eac840557ec

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates
import Theorems.Thm_JHolomorphic_exists_memLp_eq_integral_inner

namespace FMSolAux
open MeasureTheory ProbabilityTheory RiskFunctionals.Duality

section Pairing
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma pairing_eq (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing Y Z = (ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q Y Z := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]; rfl

lemma pairing_add_left (Y₁ Y₂ : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (Y₁ + Y₂) Z = pairing Y₁ Z + pairing Y₂ Z := by
  simp only [pairing_eq, map_add, ContinuousLinearMap.add_apply]

lemma pairing_sub_left (Y₁ Y₂ : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (Y₁ - Y₂) Z = pairing Y₁ Z - pairing Y₂ Z := by
  simp only [pairing_eq, map_sub, ContinuousLinearMap.sub_apply]

lemma pairing_smul_left (c : ℝ) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (c • Y) Z = c * pairing Y Z := by
  simp only [pairing_eq, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma pairing_neg_right (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing Y (-Z) = -pairing Y Z := by
  simp only [pairing_eq, map_neg]

lemma pairing_const_left (c : ℝ) (Z : Lp ℝ q P) :
    pairing (Lp.const p P c) Z = c * expectation Z := by
  unfold pairing expectation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := p) (μ := P) c] with ω hω
  rw [hω]; rfl

lemma continuous_pairing_left (Z : Lp ℝ q P) : Continuous (fun Y : Lp ℝ p P => pairing Y Z) := by
  simp only [pairing_eq]
  exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q).flip Z |>.continuous

end Pairing

section Riesz
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma memLp_one_of_two (Y : Lp ℝ 2 P) : MemLp Y 1 P :=
  (Lp.memLp Y).mono_exponent (by norm_num)

noncomputable def incl21 : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 1 P where
  toFun Y := (memLp_one_of_two Y).toLp Y
  map_add' Y₁ Y₂ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_one_of_two (Y₁ + Y₂)), Lp.coeFn_add Y₁ Y₂,
      Lp.coeFn_add ((memLp_one_of_two Y₁).toLp Y₁) ((memLp_one_of_two Y₂).toLp Y₂),
      MemLp.coeFn_toLp (memLp_one_of_two Y₁), MemLp.coeFn_toLp (memLp_one_of_two Y₂)]
      with ω h1 h2 h3 h4 h5
    rw [h1, h2, h3, Pi.add_apply, Pi.add_apply, h4, h5]
  map_smul' c Y := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_one_of_two (c • Y)), Lp.coeFn_smul c Y,
      Lp.coeFn_smul c ((memLp_one_of_two Y).toLp Y),
      MemLp.coeFn_toLp (memLp_one_of_two Y)] with ω h1 h2 h3 h4
    rw [h1, h2, RingHom.id_apply, h3, Pi.smul_apply, Pi.smul_apply, h4]

noncomputable def inclCLM : Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P :=
  (incl21 (P := P)).mkContinuous 1 fun Y => by
    rw [one_mul]
    show ‖(memLp_one_of_two Y).toLp Y‖ ≤ ‖Y‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top Y)
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable Y))

lemma inclCLM_coeFn (Y : Lp ℝ 2 P) : (inclCLM Y : Ω → ℝ) =ᵐ[P] Y :=
  MemLp.coeFn_toLp (memLp_one_of_two Y)

lemma inclCLM_ind {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) :
    inclCLM (indicatorConstLp 2 hs (measure_ne_top P s) c)
      = indicatorConstLp 1 hs (measure_ne_top P s) c := by
  apply Lp.ext
  filter_upwards [inclCLM_coeFn (indicatorConstLp 2 hs (measure_ne_top P s) c),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top P s) (c := c),
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top P s) (c := c)]
    with ω h1 h2 h3
  rw [h1, h2, h3]

lemma ind_mul_ae {r : ENNReal} {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) (g : Ω → ℝ) :
    (fun ω => (indicatorConstLp r hs (measure_ne_top P s) c : Ω → ℝ) ω * g ω)
      =ᵐ[P] s.indicator (fun ω => c * g ω) := by
  filter_upwards [indicatorConstLp_coeFn (p := r) (hs := hs) (hμs := measure_ne_top P s) (c := c)]
    with ω h
  rw [h]
  by_cases hω : ω ∈ s <;> simp [hω]

theorem riesz_one (ℓ : Lp ℝ 1 P →L[ℝ] ℝ) : ∃ Z : Lp ℝ ⊤ P, ∀ Y, ℓ Y = pairing Y Z := by
  obtain ⟨G, hG, hrep⟩ := JHolomorphic.exists_memLp_eq_integral_inner P 2 2
    (by norm_num) (by norm_num) (ℓ.comp inclCLM)
  set g : Ω → ℝ := (hG.toLp G : Ω → ℝ) with hgdef
  have hgG : g =ᵐ[P] G := MemLp.coeFn_toLp hG
  have hrep2 : ∀ Y : Lp ℝ 2 P, ℓ (inclCLM Y) = ∫ ω, Y ω * g ω ∂P := by
    intro Y
    have := hrep Y
    rw [ContinuousLinearMap.comp_apply] at this
    rw [this]
    apply integral_congr_ae
    filter_upwards [hgG] with ω hω
    rw [hω]; simp [mul_comm]
  have hgint : Integrable g P := (Lp.memLp (hG.toLp G)).integrable (by norm_num)
  set M := ‖ℓ‖
  have hset : ∀ s (hs : MeasurableSet s), ∫ ω in s, g ω ∂P = ℓ (indicatorConstLp 1 hs (measure_ne_top P s) (1 : ℝ)) := by
    intro s hs
    rw [← inclCLM_ind hs, hrep2, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [ind_mul_ae (r := 2) hs (1 : ℝ) g] with ω h
    rw [h]; simp
  have hnorm : ∀ s (hs : MeasurableSet s),
      ‖indicatorConstLp 1 hs (measure_ne_top P s) (1 : ℝ)‖ = P.real s := by
    intro s hs
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp
  have hup : g ≤ᵐ[P] fun _ => M := by
    refine ae_le_of_forall_setIntegral_le hgint (integrable_const M) fun s hs _ => ?_
    rw [hset s hs, setIntegral_const, smul_eq_mul, ← hnorm s hs, mul_comm]
    exact (le_abs_self _).trans (ℓ.le_opNorm _)
  have hlow : (fun ω => -g ω) ≤ᵐ[P] fun _ => M := by
    refine ae_le_of_forall_setIntegral_le hgint.neg (integrable_const M) fun s hs _ => ?_
    rw [integral_neg, hset s hs, setIntegral_const, smul_eq_mul, ← hnorm s hs, mul_comm]
    exact (neg_le_abs _).trans (ℓ.le_opNorm _)
  have hbd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M := by
    filter_upwards [hup, hlow] with ω h1 h2
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have hZ : MemLp g ⊤ P := memLp_top_of_bound (Lp.aestronglyMeasurable _) M hbd
  refine ⟨hZ.toLp g, ?_⟩
  have hZg : ((hZ.toLp g : Lp ℝ ⊤ P) : Ω → ℝ) =ᵐ[P] g := MemLp.coeFn_toLp hZ
  intro Y
  induction Y using Lp.induction (hp_ne_top := ENNReal.one_ne_top) with
  | @indicatorConst c s hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst]
    have e1 : ℓ (indicatorConstLp 1 hs hμs.ne c) = ∫ ω, s.indicator (fun ω => c * g ω) ω ∂P := by
      have := inclCLM_ind (P := P) hs c
      rw [← this, hrep2]
      exact integral_congr_ae (ind_mul_ae hs c g)
    rw [e1]
    unfold pairing
    apply integral_congr_ae
    filter_upwards [ind_mul_ae (r := 1) hs c (hZ.toLp g : Ω → ℝ), hZg] with ω h1 h2
    rw [h1]
    by_cases hω : ω ∈ s <;> simp [hω, h2]
  | add hf hg' _ h1 h2 =>
    rw [map_add, pairing_add_left, h1, h2]
  | isClosed =>
    exact isClosed_eq ℓ.continuous (continuous_pairing_left _)


theorem riesz {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ⊤)
    (ℓ : Lp ℝ p P →L[ℝ] ℝ) : ∃ Z : Lp ℝ q P, ∀ Y, ℓ Y = pairing Y Z := by
  rcases (Fact.out : 1 ≤ p).eq_or_lt with h1 | h1
  · subst h1
    have hq : q = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one q 1).2 rfl
    subst hq
    exact riesz_one ℓ
  · obtain ⟨G, hG, hrep⟩ := JHolomorphic.exists_memLp_eq_integral_inner P p q h1 hp ℓ
    refine ⟨hG.toLp G, fun Y => ?_⟩
    rw [hrep Y]
    unfold pairing
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hG] with ω hω
    rw [hω]; simp [mul_comm]

end Riesz

section FM
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Fenchel–Young: `h** ≤ h`. -/
lemma biconj_le (h : Lp ℝ p P → EReal) (Y : Lp ℝ p P) : convexBiconj q h Y ≤ h Y := by
  refine iSup_le fun Z => ?_
  have hc : ((pairing Y Z : ℝ) : EReal) - h Y ≤ convexConj q h Z := le_iSup (fun Y => ((pairing Y Z : ℝ) : EReal) - h Y) Y
  induction hY : h Y using EReal.rec with
  | bot =>
    rw [hY] at hc
    have : convexConj q h Z = ⊤ := by simpa using hc
    rw [this]; simp
  | coe b =>
    rw [hY] at hc
    calc ((pairing Y Z : ℝ) : EReal) - convexConj q h Z
        ≤ ((pairing Y Z : ℝ) : EReal) - (((pairing Y Z : ℝ) : EReal) - (b : EReal)) :=
          EReal.sub_le_sub le_rfl hc
      _ = b := by norm_cast; ring
  | top => exact le_top


lemma minorant_le (hR : ∀ ℓ : Lp ℝ p P →L[ℝ] ℝ, ∃ Z : Lp ℝ q P, ∀ Y, ℓ Y = pairing Y Z)
    (h : Lp ℝ p P → EReal) (ψ : Lp ℝ p P →L[ℝ] ℝ) (a : ℝ)
    (hψ : ∀ y, ((ψ y + a : ℝ) : EReal) ≤ h y) (Y : Lp ℝ p P) :
    ((ψ Y + a : ℝ) : EReal) ≤ convexBiconj q h Y := by
  obtain ⟨Z, hZ⟩ := hR ψ
  have hconj : convexConj q h Z ≤ ((-a : ℝ) : EReal) := by
    refine iSup_le fun y => ?_
    have hy0 := hψ y
    rw [← hZ y]
    induction hy : h y using EReal.rec with
    | bot => rw [hy] at hy0; simp at hy0
    | coe b =>
      rw [hy] at hy0
      have := EReal.coe_le_coe_iff.1 hy0
      rw [← EReal.coe_sub]
      exact EReal.coe_le_coe_iff.2 (by linarith)
    | top => simp
  calc ((ψ Y + a : ℝ) : EReal) = ((pairing Y Z : ℝ) : EReal) - ((-a : ℝ) : EReal) := by
        rw [hZ Y, ← EReal.coe_sub]; congr 1; ring
    _ ≤ ((pairing Y Z : ℝ) : EReal) - convexConj q h Z := EReal.sub_le_sub le_rfl hconj
    _ ≤ convexBiconj q h Y :=
        le_iSup (fun Z => ((pairing Y Z : ℝ) : EReal) - convexConj q h Z) Z

lemma epi_closed (h : Lp ℝ p P → EReal) (hlsc : LowerSemicontinuous h) :
    IsClosed (epigraph h) := by
  have := hlsc.isClosed_epigraph
  exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

lemma sep (h : Lp ℝ p P → EReal) (hproper : IsProperConvex h) (hlsc : LowerSemicontinuous h)
    (hconv : ConvexEpi h) (Y0 : Lp ℝ p P) (r : ℝ) (hr : (r : EReal) < h Y0) :
    ∃ (φ : Lp ℝ p P →L[ℝ] ℝ) (c u : ℝ), 0 ≤ c ∧ φ Y0 + r * c < u ∧
      ∀ y (b : ℝ), h y ≤ b → u < φ y + b * c := by
  have hnot : ((Y0, r) : Lp ℝ p P × ℝ) ∉ epigraph h := by
    simp only [epigraph, Set.mem_setOf_eq, not_le]; exact hr
  obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed hconv (epi_closed h hlsc) hnot
  set φ : Lp ℝ p P →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Lp ℝ p P) ℝ) with hφ
  set c : ℝ := f ((0 : Lp ℝ p P), (1 : ℝ)) with hcdef
  have hf : ∀ y s, f (y, s) = φ y + s * c := by
    intro y s
    have : ((y, s) : Lp ℝ p P × ℝ) = (y, 0) + s • ((0 : Lp ℝ p P), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hφ, hcdef]
  have hdom : ∀ y (b : ℝ), h y ≤ b → u < φ y + b * c := fun y b hb => by
    rw [← hf]; exact hfb (y, b) hb
  obtain ⟨y1, hy1⟩ := hproper.2
  obtain ⟨b1, hb1⟩ : ∃ b : ℝ, h y1 = b :=
    ⟨(h y1).toReal, (EReal.coe_toReal hy1 (hproper.1 y1)).symm⟩
  refine ⟨φ, c, u, ?_, by rw [← hf]; exact hfx, hdom⟩
  by_contra hc
  push_neg at hc
  have h1 := hdom y1 (max b1 ((u - φ y1) / c))
    (by rw [hb1]; exact EReal.coe_le_coe_iff.2 (le_max_left _ _))
  have h2 : (u - φ y1) / c ≤ max b1 ((u - φ y1) / c) := le_max_right _ _
  have h3 : max b1 ((u - φ y1) / c) * c ≤ (u - φ y1) / c * c :=
    mul_le_mul_of_nonpos_right h2 hc.le
  rw [div_mul_cancel₀ _ hc.ne] at h3
  linarith

lemma minorant_of_pos (h : Lp ℝ p P → EReal) (hproper : IsProperConvex h)
    (φ : Lp ℝ p P →L[ℝ] ℝ) (c u : ℝ) (hc : 0 < c)
    (hdom : ∀ y (b : ℝ), h y ≤ b → u < φ y + b * c) :
    ∀ y, ((((-c⁻¹) • φ) y + u / c : ℝ) : EReal) ≤ h y := by
  intro y
  induction hy : h y using EReal.rec with
  | bot => exact absurd hy (hproper.1 y)
  | coe b =>
    have h0 := hdom y b (le_of_eq hy)
    apply EReal.coe_le_coe_iff.2
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h1 : (u - φ y) / c < b := by rw [div_lt_iff₀ hc]; linarith
    have e : -c⁻¹ * φ y + u / c = (u - φ y) / c := by field_simp; ring
    rw [e]; exact h1.le
  | top => exact le_top

theorem fm_of_riesz (hR : ∀ ℓ : Lp ℝ p P →L[ℝ] ℝ, ∃ Z : Lp ℝ q P, ∀ Y, ℓ Y = pairing Y Z)
    (h : Lp ℝ p P → EReal) (hproper : IsProperConvex h)
    (hlsc : LowerSemicontinuous h) (hconv : ConvexEpi h) :
    convexBiconj q h = h := by
  funext Y0
  refine le_antisymm (biconj_le h Y0) ?_
  obtain ⟨y1, hy1⟩ := hproper.2
  obtain ⟨b1, hb1⟩ : ∃ b : ℝ, h y1 = b :=
    ⟨(h y1).toReal, (EReal.coe_toReal hy1 (hproper.1 y1)).symm⟩
  obtain ⟨φ1, c1, u1, hc1, hx1, hd1⟩ := sep h hproper hlsc hconv y1 (b1 - 1)
    (by rw [hb1]; exact EReal.coe_lt_coe_iff.2 (by linarith))
  have hc1pos : 0 < c1 := by
    have h0 := hd1 y1 b1 (le_of_eq hb1)
    rcases hc1.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at h0 hx1; simp only [mul_zero, add_zero] at h0 hx1; linarith
  have hm1 := minorant_of_pos h hproper φ1 c1 u1 hc1pos hd1
  by_contra hlt
  push_neg at hlt
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  obtain ⟨φ, c, u, hc, hx, hd⟩ := sep h hproper hlsc hconv Y0 r hr2
  rcases hc.lt_or_eq with hcpos | hc0
  · have hm := minorant_of_pos h hproper φ c u hcpos hd
    have hle := minorant_le hR h _ _ hm Y0
    have hval : r < ((-c⁻¹) • φ) Y0 + u / c := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : r < (u - φ Y0) / c := by rw [lt_div_iff₀ hcpos]; linarith
      have e : -c⁻¹ * φ Y0 + u / c = (u - φ Y0) / c := by field_simp; ring
      rw [e]; exact h1
    exact lt_irrefl _ (hr1.trans ((EReal.coe_lt_coe_iff.2 hval).trans_le hle))
  · subst hc0
    simp only [mul_zero, add_zero] at hx hd
    set ψ1 : Lp ℝ p P →L[ℝ] ℝ := (-c1⁻¹) • φ1 with hψ1
    set a1 : ℝ := u1 / c1 with ha1
    set δ := u - φ Y0 with hδdef
    have hδ : 0 < δ := by rw [hδdef]; linarith
    set m1 := ψ1 Y0 + a1 with hm1def
    set t := max 0 ((r - m1) / δ + 1) with htdef
    have ht0 : 0 ≤ t := le_max_left _ _
    have ht1 : (r - m1) / δ + 1 ≤ t := le_max_right _ _
    have hm : ∀ y, (((ψ1 + t • (-φ)) y + (a1 + t * u) : ℝ) : EReal) ≤ h y := by
      intro y
      induction hy : h y using EReal.rec with
      | bot => exact absurd hy (hproper.1 y)
      | coe b =>
        have hu := hd y b (le_of_eq hy)
        have h1 := hm1 y
        rw [hy] at h1
        have h1' := EReal.coe_le_coe_iff.1 h1
        apply EReal.coe_le_coe_iff.2
        have e : (ψ1 + t • (-φ)) y + (a1 + t * u) = (ψ1 y + a1) + t * (u - φ y) := by
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.neg_apply, smul_eq_mul]; ring
        have h2 : t * (u - φ y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
        rw [e]; linarith
      | top => exact le_top
    have hle := minorant_le hR h _ _ hm Y0
    have hval : r < (ψ1 + t • (-φ)) Y0 + (a1 + t * u) := by
      have e : (ψ1 + t • (-φ)) Y0 + (a1 + t * u) = m1 + t * δ := by
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.neg_apply, smul_eq_mul, hm1def, hδdef]; ring
      have h3 : ((r - m1) / δ + 1) * δ ≤ t * δ := mul_le_mul_of_nonneg_right ht1 hδ.le
      have e2 : ((r - m1) / δ + 1) * δ = r - m1 + δ := by field_simp
      rw [e]; linarith
    exact lt_irrefl _ (hr1.trans ((EReal.coe_lt_coe_iff.2 hval).trans_le hle))

end FM

end FMSolAux

open MeasureTheory ProbabilityTheory RiskFunctionals.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : Lp ℝ p P → EReal) (hproper : IsProperConvex h)
    (hlsc : LowerSemicontinuous h) (hconv : ConvexEpi h) :
    convexBiconj q h = h := by
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact FMSolAux.fm_of_riesz (fun ℓ => FMSolAux.riesz hp ℓ) h hproper hlsc hconv
