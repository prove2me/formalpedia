-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.theorem_5_2_existence_of_svm_solutions
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:37:09.034025+00:00
-- url     : https://prove2.me/submissions/c29dedbe-f848-44ee-a0aa-a337c968768a

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory


namespace SupportVectorMachines.InfiniteSample


/-- `ℕ` (lifted) with the trivial σ-algebra. -/
structure CxNB : Type where
  n : ULift.{0} ℕ

def CxNB.idx (x : CxNB) : ℕ := x.n.down

instance CxNB.ms : MeasurableSpace CxNB := ⊥

/-- The ℓ² Hilbert space. -/
abbrev CxH : Type := lp (fun _ : ℕ => ℝ) 2

noncomputable def cxL : Loss CxNB := fun x _ t => |t - 1| + 1 / ((x.idx : ℝ) + 1)

noncomputable def cxToFun : CxH →ₗ[ℝ] (CxNB → ℝ) where
  toFun f := fun x => f x.idx
  map_add' f g := by funext x; simp
  map_smul' c f := by funext x; simp

noncomputable def cxKAt (x : CxNB) : CxH := lp.single 2 x.idx (1 : ℝ)

noncomputable def cxK (x x' : CxNB) : ℝ := cxToFun (cxKAt x) x'

lemma cx_inner (f : CxH) (i : ℕ) : inner ℝ f (lp.single 2 i (1:ℝ)) = f i := by
  rw [lp.inner_single_right]; simp

lemma cx_rkhs : IsRKHSOfKernel CxH cxToFun cxK := by
  refine ⟨?_, cxKAt, fun x x' => rfl, ?_⟩
  · intro f g hfg
    ext n
    have := congrFun hfg (⟨⟨n⟩⟩ : CxNB)
    exact this
  · intro f x
    simp only [cxKAt]
    rw [cx_inner]; rfl

/-- Upper bound for a lower integral w.r.t. a Dirac mass on `CxNB × ℝ`
(any measurable function is constant in the first coordinate). -/
lemma cx_lintegral_le (u : CxNB × ℝ → ENNReal) (x : CxNB) :
    ∫⁻ p, u p ∂(Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) ≤ u (x, 0) := by
  obtain ⟨g, hg, hgu, heq⟩ := exists_measurable_le_lintegral_eq
    (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) u
  rw [heq, lintegral_dirac' _ hg]
  have hm : Measurable (fun z : CxNB => g (z, 0)) := hg.comp measurable_prodMk_right
  have hs : MeasurableSet[⊥] ((fun z : CxNB => g (z, 0)) ⁻¹' {g ((⟨⟨0⟩⟩ : CxNB), 0)}) :=
    hm (measurableSet_singleton _)
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with h | h
  · exfalso
    have : (⟨⟨0⟩⟩ : CxNB) ∈ ((fun z : CxNB => g (z, 0)) ⁻¹' {g ((⟨⟨0⟩⟩ : CxNB), 0)}) := rfl
    rw [h] at this; exact this
  · have : x ∈ ((fun z : CxNB => g (z, 0)) ⁻¹' {g ((⟨⟨0⟩⟩ : CxNB), 0)}) := by
      rw [h]; trivial
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    rw [← this]
    exact hgu _

theorem cx_core : ¬ (∀ {X : Type} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (lam : ℝ) (hlam : 0 < lam),
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) := by
  intro Hyp
  have hL : ∀ (x : CxNB) y, ConvexOn ℝ Set.univ (cxL x y) := by
    intro x y
    refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
    simp only [cxL, smul_eq_mul]
    have : α * a + β * b - 1 = α * (a - 1) + β * (b - 1) := by linear_combination hαβ
    rw [this]
    have h1 := abs_add_le (α * (a - 1)) (β * (b - 1))
    rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ] at h1
    have : α * (1 / ((x.idx:ℝ) + 1)) + β * (1 / ((x.idx:ℝ) + 1)) = 1 / ((x.idx:ℝ) + 1) := by
      rw [← add_mul, hαβ, one_mul]
    nlinarith
  have hLnn : ∀ (x : CxNB) y t, 0 ≤ cxL x y t := by
    intro x y t; simp only [cxL]; positivity
  have hNem : PIntegrableNemitskiLoss cxL (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) := by
    refine ⟨fun _ _ => 2, fun t => max t 0, fun _ _ => by norm_num, fun t => le_max_right _ _,
      fun a b hab => max_le_max hab le_rfl, ?_, integrable_const _⟩
    intro x y t
    simp only [cxL]
    have h1 : 1 / ((x.idx:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg x.idx : (0:ℝ) ≤ _)]
    have h2 : |t - 1| ≤ |t| + 1 := by
      have := abs_sub t 1; simpa using this
    rw [max_eq_left (abs_nonneg t)]
    linarith
  have hkBdd : ∃ M : ℝ, ∀ x : CxNB, cxK x x ≤ M := ⟨1, fun x => by
    simp [cxK, cxToFun, cxKAt, CxNB.idx]⟩
  obtain ⟨f, hf⟩ := Hyp cxL hL hLnn (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) hNem
    CxH cxToFun cxK cx_rkhs hkBdd 1 one_pos
  -- f n → 0
  have hsum : Summable (fun i => ‖f i‖ ^ (2:ENNReal).toReal) :=
    (lp.memℓp f).summable (by norm_num)
  have htend := hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/64))).exists_forall_of_atTop
  have hsmall : ∀ n, N ≤ n → |f n| ≤ 1/8 := by
    intro n hn
    have h := hN n hn
    have : (2:ENNReal).toReal = ((2:ℕ):ℝ) := by norm_num
    rw [this, Real.rpow_natCast, Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (f n)]
  set δ : ℝ := min (1/8) (1 / ((N:ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hnormf : ∀ n, (f n) ^ 2 ≤ ‖f‖ ^ 2 := by
    intro n
    have := lp.norm_apply_le_norm (by norm_num) f n
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hbound : ∀ (n : ℕ), 3/4 + δ - ‖f‖ ^ 2 ≤ |f n - 1| + 1 / ((n:ℝ) + 1) := by
    intro n
    by_cases hn : N ≤ n
    · have h1 := hsmall n hn
      have h2 : 7/8 ≤ |f n - 1| := by
        rw [abs_le] at h1
        rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
      have h3 : δ ≤ 1/8 := min_le_left _ _
      have : 0 ≤ 1 / ((n:ℝ) + 1) := by positivity
      nlinarith [sq_nonneg ‖f‖]
    · push_neg at hn
      have h3 : δ ≤ 1 / ((N:ℝ) + 1) := min_le_right _ _
      have h4 : 1 / ((N:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (n:ℝ) + 1 ≤ N := by exact_mod_cast hn
        linarith
      have h5 := hnormf n
      have h6 : 3/4 ≤ (f n)^2 + |f n - 1| := by
        rcases le_or_gt (f n) 1 with h | h
        · rw [abs_of_nonpos (by linarith)]; nlinarith [sq_nonneg (f n - 1/2)]
        · rw [abs_of_pos (by linarith)]; nlinarith
      linarith
  have hlow : ENNReal.ofReal (3/4 + δ) ≤
      ENNReal.ofReal (1 * ‖f‖ ^ 2) + populationRisk cxL
        (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) (cxToFun f) := by
    have hR : ENNReal.ofReal (3/4 + δ - ‖f‖ ^ 2) ≤ populationRisk cxL
        (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) (cxToFun f) := by
      unfold populationRisk
      calc ENNReal.ofReal (3/4 + δ - ‖f‖ ^ 2)
          = ∫⁻ _p, ENNReal.ofReal (3/4 + δ - ‖f‖ ^ 2)
              ∂(Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ _ := by
            apply lintegral_mono
            intro p
            apply ENNReal.ofReal_le_ofReal
            exact hbound p.1.idx
    calc ENNReal.ofReal (3/4 + δ) = ENNReal.ofReal (1 * ‖f‖ ^ 2 + (3/4 + δ - ‖f‖ ^ 2)) := by
          congr 1; ring
      _ ≤ ENNReal.ofReal (1 * ‖f‖ ^ 2) + ENNReal.ofReal (3/4 + δ - ‖f‖ ^ 2) :=
          ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add le_rfl hR
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδpos
  set g : CxH := lp.single 2 m (1/2 : ℝ)
  have hg := hf g
  have hgn : ‖g‖ = 1/2 := by
    simp only [g]; rw [lp.norm_single (by norm_num)]; norm_num
  have hRg : populationRisk cxL (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) (cxToFun g) ≤
      ENNReal.ofReal (1/2 + 1 / ((m:ℝ) + 1)) := by
    unfold populationRisk
    refine le_trans (cx_lintegral_le _ (⟨⟨m⟩⟩ : CxNB)) (le_of_eq ?_)
    simp only [cxL, cxToFun, LinearMap.coe_mk, AddHom.coe_mk, g, lp.single_apply_self, CxNB.idx, Pi.single_eq_same]
    norm_num
  have hup : ENNReal.ofReal (1 * ‖g‖ ^ 2) + populationRisk cxL
      (Measure.dirac ((⟨⟨0⟩⟩ : CxNB), (0:ℝ))) (cxToFun g) ≤
      ENNReal.ofReal (3/4 + 1 / ((m:ℝ) + 1)) := by
    rw [hgn]
    calc _ ≤ ENNReal.ofReal (1 * (1/2) ^ 2) + ENNReal.ofReal (1/2 + 1 / ((m:ℝ) + 1)) :=
          add_le_add le_rfl hRg
      _ = ENNReal.ofReal (3/4 + 1 / ((m:ℝ) + 1)) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
          congr 1; ring
  have := le_trans (le_trans hlow hg) hup
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
  linarith

end SupportVectorMachines.InfiniteSample

open SupportVectorMachines.InfiniteSample


theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (lam : ℝ) (hlam : 0 < lam),
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) := by
  exact cx_core
