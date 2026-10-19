-- Prove2me | solution 1 for QAlgorithms.Nannicini.fdGradient_random_point_epsSubgrad
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T04:26:55.885162+00:00
-- url     : https://prove2.me/submissions/a1f13be6-2ed0-4532-adc1-d30941f714bf

import Theorems.Thm_QAlgorithms_Nannicini_fdLaplacian_average_le
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic.Module

set_option autoImplicit false
open MeasureTheory Set QAlgorithms

private def cube {d : ℕ} (r : ℝ) : Set (Fin d → ℝ) := {x | ∀ i, |x i| ≤ r}

private lemma cube_eq {d : ℕ} (r : ℝ) :
    cube (d := d) r = Icc (fun _ => -r) (fun _ => r) := by
  ext x
  simp only [cube, mem_setOf_eq, abs_le, mem_Icc, Pi.le_def]
  exact forall_and

private lemma cube_shift {d : ℕ} {r η : ℝ} (hη : 0 < η) (hηr : η < r)
    {z : Fin d → ℝ} (hz : z ∈ cube r) (j : Fin d) :
    z + η • Pi.single j 1 ∈ cube (2*r) ∧ z - η • Pi.single j 1 ∈ cube (2*r) := by
  constructor <;> intro i
  all_goals
    have hi := abs_le.mp (hz i)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith

private lemma sqrt_bound {d : ℕ} {r : ℝ} (hr : 0 ≤ r) {z : Fin d → ℝ}
    (hz : z ∈ cube r) : Real.sqrt (∑ i, z i ^ 2) ≤ r * Real.sqrt d := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have hsum : ∑ i, z i ^ 2 ≤ (d : ℝ) * r^2 := by
      calc
        _ ≤ ∑ _i : Fin d, r^2 := Finset.sum_le_sum (fun i _ => by
          have h := mul_self_le_mul_self (abs_nonneg (z i)) (hz i)
          simpa only [←sq, sq_abs] using h)
        _ = _ := by simp
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

private lemma dual_repr {d : ℕ} (g : (Fin d → ℝ) →L[ℝ] ℝ) (x : Fin d → ℝ) :
    g x = ∑ i, g (Pi.single i 1) * x i := by
  classical
  have he : x = ∑ i, x i • Pi.single i 1 := by
    ext j; simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [he, map_sum]
  simp [map_smul, mul_comm]

private lemma lap_nonneg {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ)
    (hf : ConvexOn ℝ univ f) (z : Fin d → ℝ) : 0 ≤ fdLaplacian η f z := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (by positivity)
  have hh := hf.2 (mem_univ (z+η • Pi.single j 1))
    (mem_univ (z-η • Pi.single j 1)) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2 : ℝ)+1/2=1)
  have he : (1/2 : ℝ) • (z+η • Pi.single j 1) +
      (1/2 : ℝ) • (z-η • Pi.single j 1) = z := by module
  rw [he] at hh
  change f z ≤ 1/2 * _ + 1/2 * _ at hh
  linarith

private lemma lap_cont {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    Continuous (fdLaplacian η f) := by
  unfold fdLaplacian
  fun_prop

private lemma approximate_fd {d : ℕ} {η ε a : ℝ} (hη : 0 < η) (z : Fin d → ℝ)
    (f ft : (Fin d → ℝ) → ℝ) (g : Module.Dual ℝ (Fin d → ℝ))
    (hp : ∀ j, f z + η * g (Pi.single j 1) - a ≤ f (z+η • Pi.single j 1))
    (hm : ∀ j, f z - η * g (Pi.single j 1) - a ≤ f (z-η • Pi.single j 1))
    (hep : ∀ j, |f (z+η • Pi.single j 1)-ft (z+η • Pi.single j 1)| ≤ ε)
    (hem : ∀ j, |f (z-η • Pi.single j 1)-ft (z-η • Pi.single j 1)| ≤ ε) :
    ∑ j, |g (Pi.single j 1)-fdGradient η ft z j| ≤
      η/2 * fdLaplacian η f z + (d : ℝ)*(a+ε)/η := by
  classical
  have hη0 := hη.ne'
  have hc (j : Fin d) : |g (Pi.single j 1)-fdGradient η ft z j| ≤
      (f (z+η • Pi.single j 1)-2*f z+f (z-η • Pi.single j 1))/(2*η)+(a+ε)/η := by
    have hp' := hp j
    have hm' := hm j
    obtain ⟨hep1,hep2⟩ := abs_le.mp (hep j)
    obtain ⟨hem1,hem2⟩ := abs_le.mp (hem j)
    rw [abs_le]
    dsimp [fdGradient]
    constructor
    all_goals
      apply (mul_le_mul_iff_right₀ (show 0 < 2*η by positivity)).mp
      field_simp
      nlinarith
  calc
    _ ≤ ∑ j, ((f (z+η • Pi.single j 1)-2*f z+f (z-η • Pi.single j 1))/(2*η)+(a+ε)/η) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [fdLaplacian, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      field_simp
      ring

private lemma deterministic {d : ℕ} {r L ε η : ℝ} (hr : 0 < r) (hL : 0 < L)
    (hη : 0 < η) (hηr : η < r) (f ft : (Fin d → ℝ) → ℝ)
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hLip : ∀ y ∈ cube (2*r), ∀ y' ∈ cube (2*r),
      |f y-f y'| ≤ L*Real.sqrt (∑ i, (y i-y' i)^2))
    (hft : ∀ x ∈ cube (2*r), |f x-ft x| ≤ ε)
    (z : Fin d → ℝ) (hz : z ∈ cube r) (x : Fin d → ℝ) (hx : x ∈ cube (2*r)) :
    f 0 + (∑ j, fdGradient η ft z j * x j) -
      (2*L*r*Real.sqrt d + r*η*fdLaplacian η f z + 2*r*d*ε/η) ≤ f x := by
  classical
  apply le_of_forall_pos_le_add
  intro t ht
  let a := t / (2 + 2*r*d/η)
  have hden : 0 < 2 + 2*r*d/η := by positivity
  have ha : 0 < a := div_pos ht hden
  obtain ⟨g,c,hgc,hgz⟩ := ConvexOn.exists_affine_le_of_lt (𝕜 := ℝ)
    (s := univ) (φ := f) (x := z) (a := f z-a) (mem_univ z) (by linarith)
    isClosed_univ hc.continuousOn.lowerSemicontinuousOn hf
  have hg (y : Fin d → ℝ) : g y + c ≤ f y := by
    simpa using hgc ⟨y, mem_univ y⟩
  change g z + c = f z-a at hgz
  have hsupport (y : Fin d → ℝ) : f z + g (y-z) - a ≤ f y := by
    rw [map_sub]
    linarith [hg y]
  have hp (j : Fin d) : f z + η * g (Pi.single j 1) - a ≤ f (z+η • Pi.single j 1) := by
    have hh := hsupport (z+η • Pi.single j 1)
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hh
    linarith
  have hm (j : Fin d) : f z - η * g (Pi.single j 1) - a ≤ f (z-η • Pi.single j 1) := by
    have hh := hsupport (z-η • Pi.single j 1)
    simp only [map_sub, map_smul, smul_eq_mul] at hh
    linarith
  have hfd := approximate_fd hη z f ft g.toLinearMap hp hm
    (fun j => hft _ (cube_shift hη hηr hz j).1)
    (fun j => hft _ (cube_shift hη hηr hz j).2)
  have hpair : (∑ j, fdGradient η ft z j * x j) - g x ≤
      2*r*(η/2*fdLaplacian η f z + (d : ℝ)*(a+ε)/η) := by
    rw [dual_repr g x]
    calc
      _ = ∑ j, (fdGradient η ft z j-g (Pi.single j 1))*x j := by
        rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ ∑ j, |g (Pi.single j 1)-fdGradient η ft z j| *(2*r) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ |(fdGradient η ft z j-g (Pi.single j 1))*x j| := le_abs_self _
          _ = |g (Pi.single j 1)-fdGradient η ft z j| *|x j| := by rw [abs_mul, abs_sub_comm]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
      _ = 2*r*∑ j, |g (Pi.single j 1)-fdGradient η ft z j| := by rw [←Finset.sum_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfd (by positivity)
  have hz2 : z ∈ cube (2*r) := fun i => (hz i).trans (by linarith)
  have hzero : (0 : Fin d → ℝ) ∈ cube (2*r) := by intro i; simp; positivity
  have htwo : z+z ∈ cube (2*r) := by
    intro i; change |z i+z i| ≤ _
    calc
      _ ≤ |z i|+|z i| := abs_add_le _ _
      _ ≤ _ := by linarith [hz i]
  have hl0 := hLip 0 hzero z hz2
  have hl2 := hLip (z+z) htwo z hz2
  simp only [Pi.zero_apply, zero_sub, neg_sq] at hl0
  simp only [Pi.add_apply, add_sub_cancel_right] at hl2
  have hsqrt := sqrt_bound hr.le hz
  have hb0 : f 0-f z ≤ L*r*Real.sqrt d := by
    calc
      _ ≤ |f 0-f z| := le_abs_self _
      _ ≤ L*Real.sqrt (∑ i, z i^2) := hl0
      _ ≤ _ := by nlinarith
  have hb2 : f (z+z)-f z ≤ L*r*Real.sqrt d := by
    calc
      _ ≤ |f (z+z)-f z| := le_abs_self _
      _ ≤ L*Real.sqrt (∑ i, z i^2) := hl2
      _ ≤ _ := by nlinarith
  have hgzbound : g z ≤ L*r*Real.sqrt d+a := by
    have hh := hsupport (z+z)
    rw [show z+z-z=z by abel] at hh
    linarith
  have hxbound := hsupport x
  rw [map_sub] at hxbound
  have haeq : a*(2+2*r*d/η)=t := by dsimp [a]; field_simp
  have halgebra : 2*r*(η/2*fdLaplacian η f z+(d : ℝ)*(a+ε)/η) =
      r*η*fdLaplacian η f z+2*r*d*ε/η+(2*r*d/η)*a := by ring
  rw [halgebra] at hpair
  nlinarith

theorem solution {d : ℕ} (r L ϵ δ : ℝ) (hr : 0 < r) (hL : 0 < L)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 3) (hϵ0 : 0 < ϵ) (hϵ : ϵ < r * L * Real.sqrt d / δ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hLip : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |y i| ≤ 2 * r},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2))
    (ft : (Fin d → ℝ) → ℝ) (hft : ∀ x ∈ {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r}, |f x - ft x| ≤ ϵ)
    (η : ℝ) (hη0 : 0 < η) (hηr : η < r) :
    ϵ < 2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η ∧
    ∃ S ⊆ {z : Fin d → ℝ | ∀ i, |z i| ≤ r}, MeasurableSet S ∧
      (1 - δ) * volume.real {z : Fin d → ℝ | ∀ i, |z i| ≤ r} ≤ volume.real S ∧
      ∀ z ∈ S, IsEpsSubgradOn {x : Fin d → ℝ | ∀ i, |x i| ≤ 2 * r} f
        (2 * L * r * Real.sqrt d + η * d * L / δ + 2 * r * d * ϵ / η) 0
        (∑ j : Fin d, fdGradient η ft z j • (LinearMap.proj j : (Fin d → ℝ) →ₗ[ℝ] ℝ)) := by
  classical
  have hd : 1 ≤ d := by
    by_contra hd
    have hd0 : d = 0 := by omega
    subst d
    norm_num at hϵ
    linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : Continuous f := by
    have hh := hf.continuousOn_interior
    simpa using hh
  have hcLap := lap_cont η f hc
  have hC : MeasurableSet (cube (d := d) r) := by rw [cube_eq]; exact measurableSet_Icc
  have hfin : volume (cube (d := d) r) ≠ ⊤ := by
    rw [cube_eq]; exact isCompact_Icc.measure_lt_top.ne
  let μ := volume.restrict (cube (d := d) r)
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hfin.lt_top⟩
  let B : ℝ := d*L/(r*δ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hLip' : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |(0 : Fin d → ℝ) i-y i| ≤ r+η},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |(0 : Fin d → ℝ) i-y i| ≤ r+η},
      |f y-f y'| ≤ L*Real.sqrt (∑ i, (y i-y' i)^2) := by
    intro y hy y' hy'
    apply hLip y _ y' _
    · intro i; have hi := hy i; simp only [Pi.zero_apply, zero_sub, abs_neg] at hi; linarith
    · intro i; have hi := hy' i; simp only [Pi.zero_apply, zero_sub, abs_neg] at hi; linarith
  have hconv : Convex ℝ {y : Fin d → ℝ | ∀ i, |(0 : Fin d → ℝ) i-y i| ≤ r+η} := by
    have hh : Convex ℝ (cube (d := d) (r+η)) := by rw [cube_eq]; exact convex_Icc _ _
    simpa [cube] using hh
  have hav := QAlgorithms.Nannicini.fdLaplacian_average_le η r L hη0 hηr 0 f
    (hf.subset (subset_univ _) hconv) hLip'
  have hav' : (⨍ z, fdLaplacian η f z ∂μ) ≤ (d : ℝ)*L/r := by
    simpa [μ, cube] using hav
  have hint : Integrable (fdLaplacian η f) μ := by
    dsimp [μ]; rw [cube_eq]
    exact hcLap.continuousOn.integrableOn_Icc
  have hmass : μ.real univ = volume.real (cube (d := d) r) := by
    simp [μ]
  have hintegral : (∫ z, fdLaplacian η f z ∂μ) ≤ μ.real univ*((d : ℝ)*L/r) := by
    calc
      _ = μ.real univ*(⨍ z, fdLaplacian η f z ∂μ) := by
        simpa only [smul_eq_mul] using (measure_smul_average (μ := μ) (fdLaplacian η f)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hav' (measureReal_nonneg)
  let A := {z : Fin d → ℝ | B ≤ fdLaplacian η f z}
  have hA : MeasurableSet A := hcLap.measurable measurableSet_Ici
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall (lap_nonneg η f hf)) hint B
  have hbad : μ.real A ≤ δ*μ.real univ := by
    have he : μ.real univ*((d : ℝ)*L/r) = B*(δ*μ.real univ) := by
      dsimp [B]; field_simp <;> ring
    exact (mul_le_mul_iff_right₀ hB).mp (by
      exact hmarkov.trans (hintegral.trans_eq he))
  refine ⟨?_, cube r \ A, sdiff_subset, hC.diff hA, ?_, ?_⟩
  · have ht : ϵ < 2*r*d*ϵ/η := by
      apply (lt_div_iff₀ hη0).2
      have hde : ϵ ≤ (d : ℝ)*ϵ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hde (show 0 ≤ 2*r by positivity)]
    have ht' : 0 ≤ 2*L*r*Real.sqrt d+η*d*L/δ := by positivity
    linarith
  · have hdiff : volume.real (cube (d := d) r \ A) =
        volume.real (cube (d := d) r) - μ.real A := by
      calc
        _ = volume.real (cube (d := d) r) - volume.real (A ∩ cube r) := by
          rw [←sdiff_inter_self_eq_sdiff (s := cube (d := d) r) (t := A)]
          exact measureReal_sdiff inter_subset_right (hA.inter hC) hfin
        _ = _ := by simp only [μ, measureReal_restrict_apply hA]
    change (1-δ)*volume.real (cube (d := d) r) ≤ volume.real (cube r \ A)
    rw [hdiff]
    rw [hmass] at hbad
    linarith
  · intro z hz
    intro x hx
    have he := deterministic hr hL hη0 hηr f ft hf hc hLip hft z hz.1 x hx
    have hzB : fdLaplacian η f z ≤ B := (lt_of_not_ge hz.2).le
    have hmul := mul_le_mul_of_nonneg_left hzB (show 0 ≤ r*η by positivity)
    have hterm : r*η*B = η*d*L/δ := by dsimp [B]; field_simp <;> ring
    rw [hterm] at hmul
    simp only [sub_zero, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul] at ⊢
    linarith
