-- Prove2me | solution 1 for SX.descent_step
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:58:02.276718+00:00
-- url     : https://prove2.me/submissions/f7c8160b-f861-4a05-8b94-1fe4a6342f2a

import Definitions.Def_SX

open Complex

open NumberField
open scoped nonZeroDivisors

namespace SXD

/-- Schwarz lemma with many zeros. -/
theorem schwarz {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∀ (n : ℕ) (S : Finset ℂ), S.card = n → ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (∀ ζ ∈ S, f ζ = 0) → (∀ ζ ∈ S, ‖ζ‖ ≤ r) →
      ∀ B : ℝ, 0 ≤ B → (∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ B) →
      ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ * (R - r) ^ n ≤ B * (2 * r) ^ n := by
  have hR : (0:ℝ) < R := hr.trans hrR
  have hRr : (0:ℝ) < R - r := by linarith
  intro n
  induction n with
  | zero =>
    intro S hS f hf _ _ B hB hcirc w hw
    simp only [pow_zero, mul_one]
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0:ℂ) R)
      Metric.isBounded_ball hf.diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball (0:ℂ) hR.ne'] at hz
      exact hcirc z (by simpa [Complex.dist_eq] using hz)
    · rw [closure_ball (0:ℂ) hR.ne']
      simpa [Complex.dist_eq] using hw.trans hrR.le
  | succ n ih =>
    intro S hS f hf hzero hball B hB hcirc w hw
    obtain ⟨ζ, T, hζT, hins, hTcard⟩ := Finset.card_eq_succ.mp hS
    subst hins
    have hfζ : f ζ = 0 := hzero ζ (Finset.mem_insert_self _ _)
    have hζr : ‖ζ‖ ≤ r := hball ζ (Finset.mem_insert_self _ _)
    set g : ℂ → ℂ := dslope f ζ with hg
    have hgd : Differentiable ℂ g := by
      rw [← differentiableOn_univ] at hf ⊢
      exact (differentiableOn_dslope (Filter.univ_mem)).mpr hf
    have hfac : ∀ z : ℂ, (z - ζ) * g z = f z := by
      intro z
      simpa [hg, smul_eq_mul] using sub_smul_dslope_of_zero (f := f) (a := ζ) hfζ z
    have hgzero : ∀ ξ ∈ T, g ξ = 0 := by
      intro ξ hξ
      have h1 : (ξ - ζ) * g ξ = 0 := by
        rw [hfac]; exact hzero ξ (Finset.mem_insert_of_mem hξ)
      have h2 : ξ - ζ ≠ 0 := by
        intro h
        rw [sub_eq_zero] at h
        exact hζT (h ▸ hξ)
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hgball : ∀ ξ ∈ T, ‖ξ‖ ≤ r := fun ξ hξ => hball ξ (Finset.mem_insert_of_mem hξ)
    have hgcirc : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ ≤ B / (R - r) := by
      intro z hz
      have hzζ : ‖z - ζ‖ ≥ R - r := by
        have := norm_sub_norm_le z ζ
        rw [hz] at this; linarith
      have hzζ0 : (0:ℝ) < ‖z - ζ‖ := lt_of_lt_of_le hRr hzζ
      have : ‖z - ζ‖ * ‖g z‖ = ‖f z‖ := by rw [← norm_mul, hfac]
      rw [le_div_iff₀ hRr]
      calc ‖g z‖ * (R - r) ≤ ‖g z‖ * ‖z - ζ‖ := by
            exact mul_le_mul_of_nonneg_left hzζ (norm_nonneg _)
        _ = ‖f z‖ := by rw [mul_comm]; exact this
        _ ≤ B := hcirc z hz
    have hih := ih T hTcard g hgd hgzero hgball (B / (R - r)) (by positivity) hgcirc w hw
    have hwζ : ‖w - ζ‖ ≤ 2 * r := by
      have := norm_sub_le w ζ
      linarith [hw, hζr]
    have hfw : ‖f w‖ = ‖w - ζ‖ * ‖g w‖ := by rw [← norm_mul, hfac]
    calc ‖f w‖ * (R - r) ^ (n + 1)
        = ‖w - ζ‖ * (‖g w‖ * (R - r) ^ n) * (R - r) := by rw [hfw]; ring
      _ ≤ (2 * r) * (B / (R - r) * (2 * r) ^ n) * (R - r) := by
          apply mul_le_mul_of_nonneg_right _ hRr.le
          exact mul_le_mul hwζ hih (by positivity) (by positivity)
      _ = B * (2 * r) ^ (n + 1) := by field_simp; ring


theorem latticeSum_inj {l : ℕ} {y : Fin l → ℂ} (hy : LinearIndependent ℚ y) :
    Function.Injective (SX.latticeSum y) := by
  intro m m' h
  have hsum : ∑ j, (((m j : ℚ) - (m' j : ℚ))) • y j = 0 := by
    have e : ∑ j, (((m j : ℚ) - (m' j : ℚ))) • y j
        = SX.latticeSum y m - SX.latticeSum y m' := by
      rw [SX.latticeSum, SX.latticeSum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring
    rw [e, h, sub_self]
  have key := Fintype.linearIndependent_iff.mp hy _ hsum
  funext j
  have : ((m j : ℚ)) = ((m' j : ℚ)) := by linarith [key j]
  exact_mod_cast this

theorem norm_latticeSum_le {l : ℕ} (y : Fin l → ℂ) (m : Fin l → ℕ) (N : ℕ)
    (hm : ∀ j, m j ≤ N) : ‖SX.latticeSum y m‖ ≤ (N : ℝ) * ∑ j, ‖y j‖ := by
  calc ‖SX.latticeSum y m‖ ≤ ∑ j, ‖(m j : ℂ) * y j‖ := norm_sum_le _ _
    _ ≤ ∑ _j, (N : ℝ) * ‖y _j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm j) (norm_nonneg _)
    _ = (N : ℝ) * ∑ j, ‖y j‖ := by rw [Finset.mul_sum]

theorem norm_expExponent_le {d : ℕ} (x : Fin d → ℂ) (L : ℕ) (lam : Fin d → ℕ)
    (h : ∀ i, lam i < L) : ‖SX.expExponent x lam‖ ≤ (L : ℝ) * ∑ i, ‖x i‖ := by
  calc ‖SX.expExponent x lam‖ ≤ ∑ i, ‖(lam i : ℂ) * x i‖ := norm_sum_le _ _
    _ ≤ ∑ _i, (L : ℝ) * ‖x _i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h i).le) (norm_nonneg _)
    _ = (L : ℝ) * ∑ i, ‖x i‖ := by rw [Finset.mul_sum]

theorem norm_expSum_le {d : ℕ} (x : Fin d → ℂ) (L : ℕ) (p : (Fin d → ℕ) → ℤ) (Bp : ℝ)
    (hBp : 0 ≤ Bp) (hp : ∀ lam, |(p lam : ℝ)| ≤ Bp) (z : ℂ) :
    ‖SX.expSum x L p z‖ ≤ (L : ℝ) ^ d * Bp * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * ‖z‖) := by
  have hX : (0:ℝ) ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hterm : ∀ lam ∈ SX.box d L,
      ‖(p lam : ℂ) * Complex.exp (SX.expExponent x lam * z)‖
        ≤ Bp * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * ‖z‖) := by
    intro lam hlam
    rw [SX.mem_box] at hlam
    rw [norm_mul]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) hBp
    · simpa [Complex.norm_intCast] using hp lam
    · rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc (SX.expExponent x lam * z).re ≤ ‖SX.expExponent x lam * z‖ := Complex.re_le_norm _
        _ = ‖SX.expExponent x lam‖ * ‖z‖ := norm_mul _ _
        _ ≤ ((L : ℝ) * ∑ i, ‖x i‖) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (norm_expExponent_le x L lam hlam) (norm_nonneg _)
  calc ‖SX.expSum x L p z‖ ≤ ∑ lam ∈ SX.box d L,
        ‖(p lam : ℂ) * Complex.exp (SX.expExponent x lam * z)‖ := norm_sum_le _ _
    _ ≤ ∑ _lam ∈ SX.box d L, Bp * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * ‖z‖) :=
        Finset.sum_le_sum hterm
    _ = (L : ℝ) ^ d * Bp * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * ‖z‖) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp [SX.box, Fintype.card_piFinset]
        ring


/-- A common denominator for a finite family of elements of a number field. -/
theorem exists_denominator {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (a : ι → K) : ∃ b : K, IsIntegral ℤ b ∧ b ≠ 0 ∧ ∀ i, IsIntegral ℤ (b * a i) := by
  classical
  have hone : ∀ z : K, ∃ b : 𝓞 K, b ≠ 0 ∧ IsIntegral ℤ ((b : K) * z) := by
    intro z
    obtain ⟨b, hb⟩ := IsLocalization.exists_integer_multiple (𝓞 K)⁰ z
    refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
    obtain ⟨u, hu⟩ := hb
    have h2 : ((b : 𝓞 K) : K) * z = (u : K) := by
      rw [← Algebra.smul_def] at *
      exact hu.symm
    rw [h2]
    exact RingOfIntegers.isIntegral_coe u
  choose bO hbO0 hbOint using hone
  refine ⟨((∏ i, bO (a i) : 𝓞 K) : K), RingOfIntegers.isIntegral_coe _, ?_, ?_⟩
  · simp only [ne_eq, RingOfIntegers.coe_eq_zero_iff]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hbO0 (a i)
  · intro i
    have hsplit : ((∏ k, bO (a k) : 𝓞 K) : K) * a i
        = ((∏ k ∈ Finset.univ.erase i, bO (a k) : 𝓞 K) : K) * (((bO (a i) : 𝓞 K) : K) * a i) := by
      rw [← Finset.prod_erase_mul Finset.univ (fun k => bO (a k)) (Finset.mem_univ i)]
      push_cast
      ring
    rw [hsplit]
    exact (RingOfIntegers.isIntegral_coe _).mul (hbOint (a i))

/-- house of an indexed finite product. -/
theorem house_prod_le' {K : Type*} [Field K] [NumberField K] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K) : house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty]
      have : house (1 : K) = 1 := by
        have := house_intCast (K := K) 1
        simpa using this
      exact this.le
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (house_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (house_nonneg _))

/-- Liouville's inequality, house form. -/
theorem liouville {K : Type*} [Field K] [NumberField K] (γ : K) (hγ : IsIntegral ℤ γ)
    (hγ0 : γ ≠ 0) (σ : K →+* ℂ) :
    1 ≤ ‖σ γ‖ * house γ ^ (Module.finrank ℚ K - 1) := by
  have hA0 : (⟨γ, hγ⟩ : 𝓞 K) ≠ 0 := by
    intro h
    apply hγ0
    have h2 : algebraMap (𝓞 K) K (⟨γ, hγ⟩ : 𝓞 K) = algebraMap (𝓞 K) K 0 := congrArg _ h
    rw [map_zero] at h2
    exact h2
  have hne : Algebra.norm ℤ (⟨γ, hγ⟩ : 𝓞 K) ≠ 0 :=
    (Algebra.norm_ne_zero_iff (R := ℤ) (S := 𝓞 K)).2 hA0
  have h1 : (1 : ℝ) ≤ ‖(Algebra.norm ℚ) (algebraMap (𝓞 K) K (⟨γ, hγ⟩ : 𝓞 K))‖ := by
    rw [← Algebra.coe_norm_int (K := K) (⟨γ, hγ⟩ : 𝓞 K), ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have hcoe : algebraMap (𝓞 K) K (⟨γ, hγ⟩ : 𝓞 K) = γ := rfl
  rw [hcoe] at h1
  exact h1.trans (norm_norm_le_norm_mul_house_pow γ σ)

/-- Rewriting a monomial with the denominator distributed. -/
theorem denom_factor {K : Type*} [CommRing K] {d l : ℕ} (b : K) (α : Fin d → Fin l → K)
    (lam : Fin d → ℕ) (m : Fin l → ℕ) (E : ℕ)
    (hE : ∑ i, ∑ j, lam i * m j ≤ E) :
    b ^ E * ∏ i, ∏ j, α i j ^ (lam i * m j)
      = b ^ (E - ∑ i, ∑ j, lam i * m j) * ∏ i, ∏ j, (b * α i j) ^ (lam i * m j) := by
  have h1 : ∏ i, ∏ j, (b * α i j) ^ (lam i * m j)
      = b ^ (∑ i, ∑ j, lam i * m j) * ∏ i, ∏ j, α i j ^ (lam i * m j) := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => (Finset.prod_pow_eq_pow_sum _ _ _)
  rw [h1, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hE]



set_option maxHeartbeats 2000000 in
theorem arith_bound {d l : ℕ} (x : Fin d → ℂ) (y : Fin l → ℂ)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ), 0 < L → ∀ (p : (Fin d → ℕ) → ℤ) (Bp : ℝ), 1 ≤ Bp →
      (∀ lam, |(p lam : ℝ)| ≤ Bp) → ∀ (N : ℕ) (m : Fin l → ℕ), (∀ j, m j ≤ N) →
      SX.expSum x L p (SX.latticeSum y m) ≠ 0 →
      1 ≤ ‖SX.expSum x L p (SX.latticeSum y m)‖ *
            (((L : ℝ) ^ d * Bp) ^ (Module.finrank ℚ K)) * Real.exp (C * ((L : ℝ) * N)) := by
  classical
  haveI : NumberField K := {}
  set rk := Module.finrank ℚ K with hrkdef
  have hrk1 : 1 ≤ rk := Module.finrank_pos
  clear_value rk
  set σ : K →+* ℂ := K.val.toRingHom with hσdef
  set α : Fin d → Fin l → K := fun i j => ⟨Complex.exp (x i * y j), hK i j⟩ with hαdef
  have hσα : ∀ i j, σ (α i j) = Complex.exp (x i * y j) := fun i j => rfl
  obtain ⟨b, hbint, hb0, hbα⟩ :=
    exists_denominator (K := K) (fun ij : Fin d × Fin l => α ij.1 ij.2)
  set Hb : ℝ := max 1 (house b) with hHbdef
  set Hα : ℝ := 1 + ∑ i, ∑ j, house (b * α i j) with hHαdef
  set G : ℝ := Hb * Hα with hGdef
  have hHb1 : (1 : ℝ) ≤ Hb := le_max_left _ _
  have hHα1 : (1 : ℝ) ≤ Hα := by
    have : (0 : ℝ) ≤ ∑ i, ∑ j, house (b * α i j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => house_nonneg _
    simp only [hHαdef]; linarith
  have hG1 : (1 : ℝ) ≤ G := by
    simp only [hGdef]; nlinarith
  have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG1
  have hHbG : Hb ≤ G := by simp only [hGdef]; nlinarith
  have hHouseα : ∀ i j, house (b * α i j) ≤ Hα := by
    intro i j
    have h1 : house (b * α i j) ≤ ∑ j', house (b * α i j') :=
      Finset.single_le_sum (f := fun j' => house (b * α i j'))
        (fun _ _ => house_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j', house (b * α i j')) ≤ ∑ i', ∑ j', house (b * α i' j') :=
      Finset.single_le_sum (f := fun i' => ∑ j', house (b * α i' j'))
        (fun _ _ => Finset.sum_nonneg fun _ _ => house_nonneg _) (Finset.mem_univ i)
    simp only [hHαdef]; linarith
  have hpowG : ∀ n : ℕ, (G : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log G) := by
    intro n
    rw [Real.exp_nat_mul, Real.exp_log hG0]
  have hlogG : (0 : ℝ) ≤ Real.log G := Real.log_nonneg hG1
  have hHbhouse : house b ≤ Hb := le_max_right _ _
  clear_value G Hα Hb
  clear hHαdef hHbdef
  refine ⟨((d * l * rk : ℕ) : ℝ) * Real.log G,
    mul_nonneg (Nat.cast_nonneg _) hlogG, ?_⟩
  intro L hL p Bp hBp hp N m hm hne
  set E : ℕ := d * l * L * N with hEdef
  set w : ℂ := SX.latticeSum y m with hwdef
  set F : ℂ := SX.expSum x L p w with hFdef
  set S : (Fin d → ℕ) → ℕ := fun lam => ∑ i, ∑ j, lam i * m j with hSdef
  set βK : K := ∑ lam ∈ SX.box d L, (p lam : K) * ∏ i, ∏ j, α i j ^ (lam i * m j) with hβdef
  set δ : K := b ^ E * βK with hδdef
  -- (0) the exponent bound
  have hSE : ∀ lam ∈ SX.box d L, S lam ≤ E := by
    intro lam hlam
    rw [SX.mem_box] at hlam
    have : S lam ≤ ∑ _i : Fin d, ∑ _j : Fin l, L * N := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact Nat.mul_le_mul (hlam i).le (hm j)
    simpa [hEdef, Finset.sum_const, mul_comm, mul_assoc, mul_left_comm] using this
  -- (1) the value in K maps to F
  have hβF : σ βK = F := by
    rw [hβdef, hFdef, SX.expSum, map_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [map_mul, map_intCast, map_prod, SX.exp_expExponent_mul_latticeSum]
    refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [map_pow, hσα]
  -- (2) rewriting each monomial
  have hmono : ∀ lam ∈ SX.box d L,
      b ^ E * ((p lam : K) * ∏ i, ∏ j, α i j ^ (lam i * m j))
        = (p lam : K) * (b ^ (E - S lam) * ∏ i, ∏ j, (b * α i j) ^ (lam i * m j)) := by
    intro lam hlam
    rw [← denom_factor b α lam m E (hSE lam hlam)]
    ring
  -- (3) integrality
  have hδint : IsIntegral ℤ δ := by
    have hmem : δ ∈ integralClosure ℤ (K : Type _) := by
      rw [hδdef, hβdef, Finset.mul_sum]
      refine Subalgebra.sum_mem _ fun lam hlam => ?_
      rw [hmono lam hlam]
      have hbmem : b ∈ integralClosure ℤ (K : Type _) := hbint
      have hbαmem : ∀ i j, b * α i j ∈ integralClosure ℤ (K : Type _) :=
        fun i j => hbα (i, j)
      refine Subalgebra.mul_mem _ (by simpa using Subalgebra.algebraMap_mem _ (p lam))
        (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hbmem _) ?_)
      refine Subalgebra.prod_mem _ fun i _ => Subalgebra.prod_mem _ fun j _ => ?_
      exact Subalgebra.pow_mem _ (hbαmem i j) _
    exact hmem
  -- (4) house bound
  have hhouse : house δ ≤ (L : ℝ) ^ d * Bp * G ^ E := by
    have hterm : ∀ lam ∈ SX.box d L,
        house (b ^ E * ((p lam : K) * ∏ i, ∏ j, α i j ^ (lam i * m j))) ≤ Bp * G ^ E := by
      intro lam hlam
      rw [hmono lam hlam]
      refine le_trans (house_mul_le _ _) ?_
      have h1 : house ((p lam : K)) ≤ Bp := by
        rw [house_intCast]
        simpa using hp lam
      have hA : house (b ^ (E - S lam)) ≤ Hb ^ (E - S lam) :=
        (house_pow_le b _).trans (pow_le_pow_left₀ (house_nonneg b) hHbhouse _)
      have hB : house (∏ i, ∏ j, (b * α i j) ^ (lam i * m j)) ≤ Hα ^ S lam := by
        refine (house_prod_le' _ _).trans ?_
        have hin : ∀ i : Fin d, house (∏ j, (b * α i j) ^ (lam i * m j))
            ≤ Hα ^ (∑ j, lam i * m j) := by
          intro i
          refine (house_prod_le' _ _).trans ?_
          calc ∏ j, house ((b * α i j) ^ (lam i * m j))
              ≤ ∏ j, Hα ^ (lam i * m j) := by
                refine Finset.prod_le_prod (fun j _ => house_nonneg _) (fun j _ => ?_)
                exact (house_pow_le _ _).trans
                  (pow_le_pow_left₀ (house_nonneg _) (hHouseα i j) _)
            _ = Hα ^ (∑ j, lam i * m j) := Finset.prod_pow_eq_pow_sum _ _ _
        calc ∏ i, house (∏ j, (b * α i j) ^ (lam i * m j))
            ≤ ∏ i, Hα ^ (∑ j, lam i * m j) :=
              Finset.prod_le_prod (fun _ _ => house_nonneg _) (fun i _ => hin i)
          _ = Hα ^ S lam := Finset.prod_pow_eq_pow_sum _ _ _
      have h2 : house (b ^ (E - S lam) * ∏ i, ∏ j, (b * α i j) ^ (lam i * m j)) ≤ G ^ E := by
        refine le_trans (house_mul_le _ _) ?_
        have e1 : Hb ^ (E - S lam) ≤ Hb ^ E := pow_le_pow_right₀ hHb1 (Nat.sub_le _ _)
        have e2 : Hα ^ S lam ≤ Hα ^ E := pow_le_pow_right₀ hHα1 (hSE lam hlam)
        calc house (b ^ (E - S lam)) * house (∏ i, ∏ j, (b * α i j) ^ (lam i * m j))
            ≤ Hb ^ (E - S lam) * Hα ^ S lam :=
              mul_le_mul hA hB (house_nonneg _) (pow_nonneg (by linarith) _)
          _ ≤ Hb ^ E * Hα ^ E :=
              mul_le_mul e1 e2 (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
          _ = G ^ E := by rw [hGdef, mul_pow]
      exact mul_le_mul h1 h2 (house_nonneg _) (by linarith)
    rw [hδdef, hβdef, Finset.mul_sum]
    refine le_trans (house_sum_le_sum_house _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((SX.box d L).card : ℝ) = (L : ℝ) ^ d := by
      simp [SX.box, Fintype.card_piFinset]
    rw [this]
    ring_nf
    exact le_refl _
  -- (5) nonvanishing
  have hβ0 : βK ≠ 0 := by
    intro h
    apply hne
    rw [← hβF, h, map_zero]
  have hδ0 : δ ≠ 0 := by
    rw [hδdef]
    exact mul_ne_zero (pow_ne_zero _ hb0) hβ0
  -- (6) Liouville
  have hL1 := liouville δ hδint hδ0 σ
  rw [← hrkdef] at hL1
  have hσδ : ‖σ δ‖ ≤ Hb ^ E * ‖F‖ := by
    rw [hδdef, map_mul, map_pow, norm_mul, norm_pow, hβF]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _)
        ((norm_embedding_le_house b σ).trans hHbhouse) _) (norm_nonneg _)
  -- (7) combine
  set P : ℝ := (L : ℝ) ^ d * Bp with hPdef
  have hP1 : (1 : ℝ) ≤ P := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
    simp only [hPdef]; nlinarith
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le zero_lt_one hP1
  clear_value P
  have hstep : (1 : ℝ) ≤ ‖F‖ * P ^ rk * G ^ (E * rk) := by
    refine hL1.trans ?_
    have hhouse0 : (0 : ℝ) ≤ house δ := house_nonneg _
    have hpow : house δ ^ (rk - 1) ≤ (P * G ^ E) ^ (rk - 1) :=
      pow_le_pow_left₀ hhouse0 (by simpa [hPdef] using hhouse) _
    calc ‖σ δ‖ * house δ ^ (rk - 1)
        ≤ (Hb ^ E * ‖F‖) * (P * G ^ E) ^ (rk - 1) :=
          mul_le_mul hσδ hpow (pow_nonneg (house_nonneg _) _)
            (mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _))
      _ = ‖F‖ * (Hb ^ E * P ^ (rk - 1) * G ^ (E * (rk - 1))) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ ‖F‖ * (G ^ E * P ^ rk * G ^ (E * (rk - 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have e1 : Hb ^ E ≤ G ^ E := pow_le_pow_left₀ (by linarith) hHbG _
          have e2 : P ^ (rk - 1) ≤ P ^ rk := pow_le_pow_right₀ hP1 (Nat.sub_le _ _)
          have := mul_le_mul e1 e2 (pow_nonneg hP0.le _) (pow_nonneg hG0.le _)
          exact mul_le_mul_of_nonneg_right this (pow_nonneg hG0.le _)
      _ = ‖F‖ * P ^ rk * G ^ (E * rk) := by
          have hEE : E + E * (rk - 1) = E * rk := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hrk1
            subst hk
            simp only [Nat.add_sub_cancel_left]
            ring
          rw [← hEE, pow_add]; ring
  have hfin : G ^ (E * rk) = Real.exp ((((d * l * rk : ℕ) : ℝ) * Real.log G) * ((L : ℝ) * N)) := by
    rw [hpowG]
    congr 1
    push_cast [hEdef]
    ring
  rw [hfin] at hstep
  exact hstep


/-- The numerical endgame: `N ^ l` beats `L * N` only for bounded `N`. -/
theorem endgame {d l : ℕ} (hdl : d + l < d * l) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {L N M : ℕ} (hN : 0 < N) (hLc : (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l) (hMN : M ≤ N)
    (h : ((N : ℝ) ^ l) * Real.log 2 ≤ C * ((L : ℝ) * N)) :
    (N : ℝ) * (Real.log 2) ^ d ≤ C ^ d * c := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : (((N : ℝ) ^ l) * Real.log 2) ^ d ≤ (C * ((L : ℝ) * N)) ^ d :=
    pow_le_pow_left₀ (by positivity) h d
  have hLHS : (((N : ℝ) ^ l) * Real.log 2) ^ d = (N : ℝ) ^ (l * d) * (Real.log 2) ^ d := by
    rw [mul_pow, ← pow_mul]
  have hRHS : (C * ((L : ℝ) * N)) ^ d = C ^ d * ((L : ℝ) ^ d) * (N : ℝ) ^ d := by
    rw [mul_pow, mul_pow]; ring
  have hMle : (M : ℝ) ^ l ≤ (N : ℝ) ^ l :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hMN) l
  have hstep : C ^ d * ((L : ℝ) ^ d) * (N : ℝ) ^ d ≤ C ^ d * c * (N : ℝ) ^ l * (N : ℝ) ^ d := by
    have hA : C ^ d * ((L : ℝ) ^ d) ≤ C ^ d * (c * (N : ℝ) ^ l) := by
      refine mul_le_mul_of_nonneg_left (hLc.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hMle hc.le
    calc C ^ d * ((L : ℝ) ^ d) * (N : ℝ) ^ d ≤ C ^ d * (c * (N : ℝ) ^ l) * (N : ℝ) ^ d :=
          mul_le_mul_of_nonneg_right hA (by positivity)
      _ = C ^ d * c * (N : ℝ) ^ l * (N : ℝ) ^ d := by ring
  have hmain : (N : ℝ) ^ (l * d) * (Real.log 2) ^ d ≤ C ^ d * c * (N : ℝ) ^ (l + d) := by
    rw [pow_add]
    calc (N : ℝ) ^ (l * d) * (Real.log 2) ^ d = (((N : ℝ) ^ l) * Real.log 2) ^ d := hLHS.symm
      _ ≤ (C * ((L : ℝ) * N)) ^ d := h1
      _ = C ^ d * ((L : ℝ) ^ d) * (N : ℝ) ^ d := hRHS
      _ ≤ C ^ d * c * (N : ℝ) ^ l * (N : ℝ) ^ d := hstep
      _ = C ^ d * c * ((N : ℝ) ^ l * (N : ℝ) ^ d) := by ring
  obtain ⟨q, hq⟩ : ∃ q, d * l = q := ⟨_, rfl⟩
  rw [hq] at hdl
  have hqld : l * d = q := by rw [mul_comm]; exact hq
  obtain ⟨k, hk1, hk2⟩ : ∃ k, 1 ≤ k ∧ l * d = k + (l + d) := ⟨q - (l + d), by omega, by omega⟩
  rw [hk2, pow_add] at hmain
  have hpos : (0 : ℝ) < (N : ℝ) ^ (l + d) := by positivity
  have hcancel : (N : ℝ) ^ k * (Real.log 2) ^ d ≤ C ^ d * c := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc (N : ℝ) ^ k * (Real.log 2) ^ d * (N : ℝ) ^ (l + d)
        = (N : ℝ) ^ k * (N : ℝ) ^ (l + d) * (Real.log 2) ^ d := by ring
      _ ≤ C ^ d * c * (N : ℝ) ^ (l + d) := hmain
  have hNk : (N : ℝ) ≤ (N : ℝ) ^ k := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast hN) hk1
  nlinarith [pow_pos hlog2 d]

end SXD

set_option maxHeartbeats 2000000 in
open SX in
theorem solution
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K)
    (c : ℝ) (hc : 0 < c) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ L : ℕ, 0 < L → (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l →
      ∀ p : (Fin d → ℕ) → ℤ, (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) →
        ∀ N : ℕ, M ≤ N →
          (∀ m : Fin l → ℕ, (∀ j, m j < N) → SX.expSum x L p (SX.latticeSum y m) = 0) →
          (∀ m : Fin l → ℕ, (∀ j, m j < N + 1) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  obtain ⟨C₂, hC₂0, harith⟩ := SXD.arith_bound x y K hK
  have hX0 : (0 : ℝ) ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hY0 : (0 : ℝ) ≤ ∑ j, ‖y j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set rk : ℕ := Module.finrank ℚ K with hrkdef
  set C : ℝ := ((rk : ℝ) + 1) * ((d : ℝ) + c)
      + 5 * (∑ i, ‖x i‖) * ((∑ j, ‖y j‖) + 1) + C₂ with hCdef
  have hC0 : (0 : ℝ) ≤ C := by
    have h1 : (0 : ℝ) ≤ ((rk : ℝ) + 1) * ((d : ℝ) + c) :=
      mul_nonneg (by positivity) (add_nonneg (Nat.cast_nonneg d) hc.le)
    have h2 : (0 : ℝ) ≤ 5 * (∑ i, ‖x i‖) * ((∑ j, ‖y j‖) + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hX0) (by linarith)
    simp only [hCdef]; linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set Z : ℝ := C ^ d * c / (Real.log 2) ^ d with hZdef
  refine ⟨max 1 (⌈Z⌉₊ + 1), ?_⟩
  intro M hM L hL hLc p hp N hMN hvan m hm
  by_contra hFne
  have hM1 : 1 ≤ M := le_trans (le_max_left 1 _) hM
  have hN1 : 1 ≤ N := le_trans hM1 hMN
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0' : (0 : ℝ) ≤ (L : ℝ) := by positivity
  set Bp : ℝ := Real.exp (c * L * M) with hBpdef
  have hBp1 : (1 : ℝ) ≤ Bp := Real.one_le_exp (by positivity)
  set r : ℝ := (N : ℝ) * (∑ j, ‖y j‖) + 1 with hrdef
  have hr0 : (0 : ℝ) < r := by positivity
  set R : ℝ := 5 * r with hRdef
  have hrR : r < R := by simp only [hRdef]; linarith
  set n : ℕ := N ^ l with hndef
  set SS : Finset ℂ := (SX.box l N).image (SX.latticeSum y) with hSSdef
  have hcard : SS.card = n := by
    rw [hSSdef, Finset.card_image_of_injective _ (SXD.latticeSum_inj hy), hndef]
    simp [SX.box, Fintype.card_piFinset]
  have hzeros : ∀ ζ ∈ SS, SX.expSum x L p ζ = 0 := by
    intro ζ hζ
    rw [hSSdef, Finset.mem_image] at hζ
    obtain ⟨m', hm', rfl⟩ := hζ
    exact hvan m' (by simpa [SX.mem_box] using hm')
  have hballs : ∀ ζ ∈ SS, ‖ζ‖ ≤ r := by
    intro ζ hζ
    rw [hSSdef, Finset.mem_image] at hζ
    obtain ⟨m', hm', rfl⟩ := hζ
    rw [SX.mem_box] at hm'
    have := SXD.norm_latticeSum_le y m' N (fun j => (hm' j).le)
    simp only [hrdef]; linarith
  set B : ℝ := (L : ℝ) ^ d * Bp * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * R) with hBdef
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hcirc : ∀ z : ℂ, ‖z‖ = R → ‖SX.expSum x L p z‖ ≤ B := by
    intro z hz
    have h := SXD.norm_expSum_le x L p Bp (by linarith) hp z
    rw [hz] at h
    exact h
  have hw : ‖SX.latticeSum y m‖ ≤ r := by
    have := SXD.norm_latticeSum_le y m N (fun j => Nat.lt_succ_iff.mp (hm j))
    simp only [hrdef]; linarith
  have hsch := SXD.schwarz hr0 hrR n SS hcard (SX.expSum x L p)
    (SX.differentiable_expSum x L p) hzeros hballs B hB0 hcirc _ hw
  have h2r : (0 : ℝ) < (2 * r) ^ n := by positivity
  have hRr : (R - r) ^ n = 2 ^ n * (2 * r) ^ n := by
    rw [hRdef, show (5 * r - r : ℝ) = 2 * (2 * r) by ring, mul_pow]
  have hanal : ‖SX.expSum x L p (SX.latticeSum y m)‖ * 2 ^ n ≤ B := by
    rw [hRr] at hsch
    refine le_of_mul_le_mul_right ?_ h2r
    calc ‖SX.expSum x L p (SX.latticeSum y m)‖ * 2 ^ n * (2 * r) ^ n
        = ‖SX.expSum x L p (SX.latticeSum y m)‖ * (2 ^ n * (2 * r) ^ n) := by ring
      _ ≤ B * (2 * r) ^ n := hsch
  have harith' := harith L hL p Bp hBp1 hp N m (fun j => Nat.lt_succ_iff.mp (hm j)) hFne
  set P : ℝ := (L : ℝ) ^ d * Bp with hPdef
  have hP0 : (0 : ℝ) < P := by positivity
  have hE2 : (0 : ℝ) < Real.exp (C₂ * ((L : ℝ) * N)) := Real.exp_pos _
  have hkey : (2 : ℝ) ^ n ≤ B * P ^ rk * Real.exp (C₂ * ((L : ℝ) * N)) := by
    calc (2 : ℝ) ^ n = 2 ^ n * 1 := (mul_one _).symm
      _ ≤ 2 ^ n * (‖SX.expSum x L p (SX.latticeSum y m)‖ * P ^ rk
            * Real.exp (C₂ * ((L : ℝ) * N))) :=
          mul_le_mul_of_nonneg_left harith' (by positivity)
      _ = (‖SX.expSum x L p (SX.latticeSum y m)‖ * 2 ^ n)
            * (P ^ rk * Real.exp (C₂ * ((L : ℝ) * N))) := by ring
      _ ≤ B * (P ^ rk * Real.exp (C₂ * ((L : ℝ) * N))) :=
          mul_le_mul_of_nonneg_right hanal (by positivity)
      _ = B * P ^ rk * Real.exp (C₂ * ((L : ℝ) * N)) := by ring
  -- turn the right-hand side into a single exponential
  have hPle : P ≤ Real.exp (((d : ℝ) + c) * ((L : ℝ) * N)) := by
    have hLexp : (L : ℝ) ≤ Real.exp ((L : ℝ) * N) := by
      have h1 : (L : ℝ) ≤ (L : ℝ) * N := le_mul_of_one_le_right hL0' hN1'
      have h2 : (L : ℝ) * N ≤ Real.exp ((L : ℝ) * N) := by
        have := Real.add_one_le_exp ((L : ℝ) * N); linarith
      linarith
    have hA : (L : ℝ) ^ d ≤ Real.exp ((d : ℝ) * ((L : ℝ) * N)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ hL0' hLexp d
    have hB' : Bp ≤ Real.exp (c * ((L : ℝ) * N)) := by
      rw [hBpdef]
      refine Real.exp_le_exp.mpr ?_
      have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
      have hcl : (0 : ℝ) ≤ c * L := mul_nonneg hc.le hL0'
      nlinarith [hcl, hMN']
    calc P = (L : ℝ) ^ d * Bp := hPdef
      _ ≤ Real.exp ((d : ℝ) * ((L : ℝ) * N)) * Real.exp (c * ((L : ℝ) * N)) :=
          mul_le_mul hA hB' (by positivity) (Real.exp_pos _).le
      _ = Real.exp (((d : ℝ) + c) * ((L : ℝ) * N)) := by rw [← Real.exp_add]; ring_nf
  have hfinal : (2 : ℝ) ^ n ≤ Real.exp (C * ((L : ℝ) * N)) := by
    refine hkey.trans ?_
    have hBP : B = P * Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * R) := by rw [hBdef, hPdef]
    have h1 : B * P ^ rk * Real.exp (C₂ * ((L : ℝ) * N))
        = P ^ (rk + 1) * (Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * R)
            * Real.exp (C₂ * ((L : ℝ) * N))) := by
      rw [hBP, pow_succ]; ring
    rw [h1]
    have e1 : P ^ (rk + 1) ≤ Real.exp ((((rk : ℝ) + 1) * ((d : ℝ) + c)) * ((L : ℝ) * N)) := by
      have := pow_le_pow_left₀ hP0.le hPle (rk + 1)
      rw [← Real.exp_nat_mul] at this
      refine this.trans (Real.exp_le_exp.mpr ?_)
      push_cast
      ring_nf
      exact le_refl _
    have e2 : Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * R)
        ≤ Real.exp ((5 * (∑ i, ‖x i‖) * ((∑ j, ‖y j‖) + 1)) * ((L : ℝ) * N)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hRdef, hrdef]
      nlinarith [mul_nonneg (mul_nonneg hL0' hX0) (by linarith : (0:ℝ) ≤ (N : ℝ) - 1),
        mul_nonneg hL0' hX0, hY0, hX0]
    calc P ^ (rk + 1) * (Real.exp (((L : ℝ) * ∑ i, ‖x i‖) * R)
            * Real.exp (C₂ * ((L : ℝ) * N)))
        ≤ Real.exp ((((rk : ℝ) + 1) * ((d : ℝ) + c)) * ((L : ℝ) * N))
            * (Real.exp ((5 * (∑ i, ‖x i‖) * ((∑ j, ‖y j‖) + 1)) * ((L : ℝ) * N))
              * Real.exp (C₂ * ((L : ℝ) * N))) := by
          refine mul_le_mul e1 ?_ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
      _ = Real.exp (C * ((L : ℝ) * N)) := by
          rw [← Real.exp_add, ← Real.exp_add, hCdef]; ring_nf
  have h2n : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h2n, Real.exp_le_exp] at hfinal
  have hnN : (n : ℝ) = (N : ℝ) ^ l := by rw [hndef]; push_cast; ring
  rw [hnN] at hfinal
  have hend := SXD.endgame hdl hC0 hc (Nat.lt_of_lt_of_le Nat.zero_lt_one hN1) hLc hMN hfinal
  have hNZ : (N : ℝ) ≤ Z := by
    rw [hZdef, le_div_iff₀ (by positivity)]
    exact hend
  have hbig : ((⌈Z⌉₊ : ℝ) + 1) ≤ (N : ℝ) := by
    have h : (⌈Z⌉₊ + 1 : ℕ) ≤ N := le_trans (le_trans (le_max_right 1 _) hM) hMN
    exact_mod_cast h
  have := Nat.le_ceil Z
  linarith
