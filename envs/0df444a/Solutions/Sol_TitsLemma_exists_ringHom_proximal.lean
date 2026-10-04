-- Prove2me | solution 1 for TitsLemma.exists_ringHom_proximal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:24.771178+00:00
-- url     : https://prove2.me/submissions/19ffbfb2-7568-4a96-a9c6-dc3f8e5d7f30

import Mathlib


section
section
open MeasureTheory Matrix Filter Topology

namespace TitsLemma

open Cardinal Polynomial

/-- Extension of an injective ring hom from a subring of a countable field into an uncountable
algebraically closed field. -/
theorem exists_ringHom_extend {K Ω : Type} [Field K] [Countable K] [Field Ω] [IsAlgClosed Ω]
    (hΩ : ℵ₀ < #Ω) (R₀ : Subring K) (τ : R₀ →+* Ω) (hτ : Function.Injective τ) :
    ∃ σ : K →+* Ω, ∀ r : R₀, σ r = τ r := by
  let _ : Algebra R₀ Ω := τ.toAlgebra
  have : FaithfulSMul R₀ Ω := (faithfulSMul_iff_algebraMap_injective R₀ Ω).2 hτ
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis R₀ K
  obtain ⟨C, hC⟩ := exists_isTranscendenceBasis R₀ Ω
  have hR₀ : #R₀ ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hBc : #B ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hCc : ℵ₀ < #C := by
    by_contra h
    push Not at h
    have := IsAlgClosed.cardinal_le_max_transcendence_basis' _ hC
    have : #Ω ≤ ℵ₀ := this.trans (max_le (max_le hR₀ h) le_rfl)
    exact absurd hΩ (not_lt.2 this)
  obtain ⟨e⟩ : Nonempty (B ↪ C) := (Cardinal.le_def _ _).1 (hBc.trans hCc.le)
  let y : B → Ω := fun b => (e b : Ω)
  have hy : AlgebraicIndependent R₀ y := hC.1.comp _ e.injective
  let R₁ := Algebra.adjoin R₀ (Set.range ((↑) : B → K))
  let φ : R₁ →ₐ[R₀] Ω := (MvPolynomial.aeval y).comp hB.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (show Function.Injective (MvPolynomial.aeval (R := R₀) y) from hy).comp
      hB.1.aevalEquiv.symm.injective
  let _ : Algebra R₁ Ω := φ.toRingHom.toAlgebra
  have : FaithfulSMul R₁ Ω := (faithfulSMul_iff_algebraMap_injective R₁ Ω).2 hφ
  have : Algebra.IsAlgebraic R₁ K := hB.isAlgebraic
  let σ : K →ₐ[R₁] Ω := IsAlgClosed.lift
  refine ⟨σ.toRingHom, fun r => ?_⟩
  have h1 := σ.commutes (algebraMap R₀ R₁ r)
  have h2 : algebraMap R₁ K (algebraMap R₀ R₁ r) = (r : K) := rfl
  have h3 : algebraMap R₁ Ω (algebraMap R₀ R₁ r) = τ r := φ.commutes r
  rw [h2, h3] at h1
  exact h1

/-- A ring hom out of `ℤ[t]` determined by the value at `t`, injective when the annihilators
agree. -/
theorem exists_hom_closure_inj {R K : Type*} [CommRing R] [CommRing K] (t : R) (y : K)
    (h : ∀ p : ℤ[X], aeval t p = 0 ↔ aeval y p = 0) :
    ∃ σ : Subring.closure ({t} : Set R) →+* K, Function.Injective σ ∧
      σ ⟨t, Subring.subset_closure rfl⟩ = y := by
  let f : ℤ[X] →+* R := (aeval t : ℤ[X] →ₐ[ℤ] R).toRingHom
  let g : ℤ[X] →+* K := (aeval y : ℤ[X] →ₐ[ℤ] K).toRingHom
  have hle : Subring.closure ({t} : Set R) ≤ f.range :=
    Subring.closure_le.mpr (Set.singleton_subset_iff.mpr ⟨X, by simp [f]⟩)
  have hker : RingHom.ker f ≤ RingHom.ker g := fun p hp => by
    simp only [RingHom.mem_ker] at hp ⊢
    exact (h p).1 hp
  have hker' : RingHom.ker g ≤ RingHom.ker f := fun p hp => by
    simp only [RingHom.mem_ker] at hp ⊢
    exact (h p).2 hp
  refine ⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp
    ((f.quotientKerEquivRange.symm.toRingHom).comp (Subring.inclusion hle)), ?_, ?_⟩
  · exact (RingHom.lift_injective_of_ker_le_ideal _ hker hker').comp
      (f.quotientKerEquivRange.symm.injective.comp (Subring.inclusion_injective hle))
  have h1 : f.quotientKerEquivRange.symm (Subring.inclusion hle ⟨t, Subring.subset_closure rfl⟩)
      = Ideal.Quotient.mk _ X := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    show t = f X
    simp [f]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h1]
  simp [g]

theorem countable_closure (s : Finset ℝ) : Countable (Subfield.closure (s : Set ℝ)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Subfield.cardinalMk_closure_le_max _).trans
    (max_le (Cardinal.lt_aleph0_of_finite _).le le_rfl)

/-- Reduction: a value `μ` in an uncountable algebraically closed normed field with the same
annihilator for `μ + μ⁻¹` as for `t` gives the conclusion. -/
theorem reduce (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    {Ω : Type} [NormedField Ω] [IsAlgClosed Ω] (hΩ : ℵ₀ < #Ω) (μ : Ω) (hμ : 1 < ‖μ‖)
    (h : ∀ p : ℤ[X], aeval t p = 0 ↔ aeval (μ + μ⁻¹) p = 0) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  have := countable_closure s
  set K := Subfield.closure (s : Set ℝ) with hK
  let x : K := ⟨t, hts⟩
  have hx : ∀ p : ℤ[X], aeval x p = 0 ↔ aeval (μ + μ⁻¹) p = 0 := by
    intro p
    rw [← h p]
    have : ((aeval x p : K) : ℝ) = aeval t p := by
      simpa using (Polynomial.aeval_algHom_apply (K.subtype.toIntAlgHom) x p).symm
    rw [← this]
    exact ⟨fun h0 => by rw [h0]; rfl, fun h0 => Subtype.ext h0⟩
  obtain ⟨τ, hτinj, hτ⟩ := exists_hom_closure_inj x (μ + μ⁻¹) hx
  obtain ⟨σ, hσ⟩ := exists_ringHom_extend hΩ (Subring.closure {x}) τ hτinj
  refine ⟨Ω, inferInstance, σ, μ, hμ, ?_⟩
  rw [← hτ, ← hσ]

theorem exists_add_inv_eq {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (a : Ω) :
    ∃ μ : Ω, μ ≠ 0 ∧ μ + μ⁻¹ = a := by
  have hdeg : (X ^ 2 - C a * X + 1 : Polynomial Ω).degree = 2 := by compute_degree!
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (X ^ 2 - C a * X + 1 : Polynomial Ω) (by rw [hdeg]; decide)
  have h : μ ^ 2 - a * μ + 1 = 0 := by simpa [IsRoot] using hμ
  have h0 : μ ≠ 0 := by rintro rfl; simp at h
  refine ⟨μ, h0, ?_⟩
  field_simp
  linear_combination h

theorem aeval_iff_of_minpoly {Ω : Type*} [Field Ω] [Algebra ℚ Ω] (t : ℝ) (ht : IsIntegral ℚ t)
    (t' : Ω) (ht' : aeval t' (minpoly ℚ t) = 0) (p : ℤ[X]) :
    aeval t p = 0 ↔ aeval t' p = 0 := by
  have heq : minpoly ℚ t = minpoly ℚ t' :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible ht) ht' (minpoly.monic ht)
  rw [← aeval_map_algebraMap ℚ, ← aeval_map_algebraMap ℚ (x := t'), ← minpoly.dvd_iff,
    ← minpoly.dvd_iff, heq]

theorem aleph0_lt_mk_complex : ℵ₀ < #ℂ := by
  rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum

/-- Case 1: `t` transcendental. -/
theorem case_transcendental (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (ht : Transcendental ℤ t) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  set l := liouvilleNumber 2
  have hl : Transcendental ℤ l := transcendental_liouvilleNumber le_rfl
  obtain ⟨n, hn⟩ := exists_nat_gt (2 - l)
  set r : ℝ := l + n with hr_def
  have hr2 : 2 < r := by rw [hr_def]; linarith
  have hr : Transcendental ℤ r := by
    have := hl.aeval (X + C (n : ℤ)) (by rw [natDegree_X_add_C]; exact one_ne_zero)
      (by rw [leadingCoeff_X_add_C]; exact one_mem _)
    simpa [hr_def] using this
  set q : ℝ := Real.sqrt (r ^ 2 - 4)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = r ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
  set m : ℝ := (r + q) / 2 with hm_def
  have hm1 : 1 < m := by rw [hm_def]; linarith
  have hmul : m * ((r - q) / 2) = 1 := by rw [hm_def]; linear_combination (-1 / 4 : ℝ) * hq2
  have hminv : m⁻¹ = (r - q) / 2 := inv_eq_of_mul_eq_one_right hmul
  have hmr : m + m⁻¹ = r := by rw [hminv, hm_def]; ring
  refine reduce s t hts aleph0_lt_mk_complex (m : ℂ) ?_ ?_
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hm1
  intro p
  have e : (m : ℂ) + (m : ℂ)⁻¹ = algebraMap ℝ ℂ r := by
    rw [← hmr]; simp
  rw [e, aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℝ ℂ).injective]
  rw [transcendental_iff] at ht hr
  constructor
  · intro h0; rw [ht p h0, map_zero]
  · intro h0; rw [hr p h0, map_zero]

/-- Case 2: `t` an algebraic integer (Kronecker). -/
theorem case_integral (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (hint : IsIntegral ℤ t)
    (hinf : ∀ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → (t : ℂ) ≠ z + z⁻¹) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  have htQ : IsIntegral ℚ t := hint.tower_top
  set P := minpoly ℚ t with hP
  suffices H : ∃ μ : ℂ, 1 < ‖μ‖ ∧ aeval (μ + μ⁻¹) P = 0 by
    obtain ⟨μ, hμ, hPμ⟩ := H
    exact reduce s t hts aleph0_lt_mk_complex μ hμ (aeval_iff_of_minpoly t htQ _ hPμ)
  by_contra H
  push Not at H
  obtain ⟨l, hl0, hlt⟩ := exists_add_inv_eq (t : ℂ)
  have htC : IsIntegral ℤ (t : ℂ) := by
    have := hint.map ((Algebra.ofId ℝ ℂ).restrictScalars ℤ)
    simpa using this
  have hlint : IsIntegral ℤ l := by
    let A := integralClosure ℤ ℂ
    have htA : (t : ℂ) ∈ A := htC
    refine isIntegral_trans (A := A) l ⟨X ^ 2 - C ⟨(t : ℂ), htA⟩ * X + 1, by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, map_one]
    show l ^ 2 - (t : ℂ) * l + 1 = 0
    rw [← hlt]
    field_simp
    ring
  have hlQ : IsIntegral ℚ l := hlint.tower_top
  let E := IntermediateField.adjoin ℚ ({l} : Set ℂ)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hlQ
  have : NumberField E := ⟨⟩
  let x : E := IntermediateField.AdjoinSimple.gen ℚ l
  have hx : (x : ℂ) = l := rfl
  have hx0 : x ≠ 0 := fun h => hl0 (by rw [← hx, h]; rfl)
  have hxi : IsIntegral ℤ x := by
    refine (isIntegral_algHom_iff ((IntermediateField.val E).toRingHom.toIntAlgHom)
      Subtype.val_injective).1 ?_
    exact hlint
  have hxt : aeval (x + x⁻¹) P = 0 := by
    have h1 := Polynomial.aeval_algHom_apply (IntermediateField.val E) (x + x⁻¹) P
    have h2 : (IntermediateField.val E) (x + x⁻¹) = algebraMap ℝ ℂ t := by
      simp only [map_add, map_inv₀]
      rw [IntermediateField.coe_val, hx, hlt]
      rfl
    rw [h2, aeval_algebraMap_apply, hP, minpoly.aeval, map_zero] at h1
    exact Subtype.ext h1.symm
  obtain ⟨n, hn, hxn⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0 hxi (fun φ => by
    by_contra hφ
    push Not at hφ
    apply H (φ x) hφ
    have h3 : φ x + (φ x)⁻¹ = φ.toRatAlgHom (x + x⁻¹) := by simp [map_add, map_inv₀]
    rw [h3, Polynomial.aeval_algHom_apply, hxt, map_zero])
  apply hinf l ⟨n, hn, ?_⟩ hlt.symm
  have := congrArg ((↑) : E → ℂ) hxn
  simpa [hx] using this

/-- The closed unit ball of an ultrametric normed field, as a subring. -/
def unitBall (F : Type*) [NormedField F] [IsUltrametricDist F] : Subring F where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

/-- A rational number with `p ∣ den` has `p`-adic norm `> 1`. -/
theorem one_lt_padicNorm (c : ℚ) (p : ℕ) [Fact p.Prime] (hpd : p ∣ c.den) :
    1 < ‖(c : ℚ_[p])‖ := by
  have hp : p.Prime := Fact.out
  have hnum : ¬ ((p : ℤ) ∣ c.num) := by
    intro h
    have h' : p ∣ c.num.natAbs := Int.natCast_dvd.1 h
    have := Nat.dvd_gcd h' hpd
    rw [c.reduced] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have h1 : ‖(c.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.1 fun h => hnum (Padic.norm_intCast_lt_one_iff.1 h))
  have h2 : ‖(c.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.2 hpd
  have h3 : 0 < ‖(c.den : ℚ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 c.den_nz)
  rw [Rat.cast_def, norm_div, h1]
  exact (one_lt_div h3).2 h2

theorem aleph0_lt_mk_padicAlgCl (p : ℕ) [Fact p.Prime] : ℵ₀ < #(PadicAlgCl p) :=
  Cardinal.aleph0_lt_continuum.trans_le (continuum_le_cardinal_of_module ℚ_[p] (PadicAlgCl p))

/-- Case 3: `t` algebraic but not an algebraic integer (a `p`-adic place). -/
theorem case_nonintegral (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (halg : IsAlgebraic ℤ t) (hint : ¬IsIntegral ℤ t) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  have htQ : IsIntegral ℚ t := (halg.extendScalars (algebraMap ℤ ℚ).injective_int).isIntegral
  set P := minpoly ℚ t with hP
  obtain ⟨n, hn⟩ : ∃ n, P.coeff n ∉ Set.range (algebraMap ℤ ℚ) := by
    by_contra H
    push Not at H
    have hl : P ∈ lifts (algebraMap ℤ ℚ) := (lifts_iff_coeff_lifts P).2 H
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic htQ)
    exact hint ⟨Q, hQm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ, hQ, hP, minpoly.aeval]⟩
  set c := P.coeff n with hc
  have hden : c.den ≠ 1 := fun h => hn ⟨c.num, by simp [(Rat.den_eq_one_iff c).1 h]⟩
  set p := c.den.minFac
  have : Fact p.Prime := ⟨Nat.minFac_prime hden⟩
  have hcp : 1 < ‖(c : ℚ_[p])‖ := one_lt_padicNorm c p (Nat.minFac_dvd _)
  set Ω := PadicAlgCl p
  set P' := P.map (algebraMap ℚ Ω) with hP'
  have hmon : P'.Monic := (minpoly.monic htQ).map _
  have hprod := (IsAlgClosed.splits P').eq_prod_roots_of_monic hmon
  obtain ⟨r, hr, hr1⟩ : ∃ r ∈ P'.roots, 1 < ‖r‖ := by
    by_contra H
    push Not at H
    have hlift : P' ∈ lifts (unitBall Ω).subtype := by
      rw [hprod]
      refine Subsemiring.multiset_prod_mem _ _ (fun q hq => ?_)
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hq
      rw [sub_eq_add_neg, ← C_neg]
      exact add_mem (X_mem_lifts _) (C'_mem_lifts ⟨⟨-a, by simpa [unitBall] using H a ha⟩, rfl⟩)
    obtain ⟨⟨b, hb⟩, hb'⟩ := (lifts_iff_coeff_lifts _).1 hlift n
    have hb1 : ‖P'.coeff n‖ ≤ 1 := by
      rw [← hb']; exact hb
    rw [hP', coeff_map, ← hc, eq_ratCast, ← map_ratCast (algebraMap ℚ_[p] Ω),
      PadicAlgCl.norm_extends] at hb1
    linarith
  have hr' : aeval r P = 0 := by
    rw [hP', mem_roots hmon.ne_zero, IsRoot, eval_map_algebraMap] at hr
    exact hr
  obtain ⟨μ, hμ0, hμ⟩ := exists_add_inv_eq r
  have key : 1 < ‖μ‖ ∨ 1 < ‖μ⁻¹‖ := by
    by_contra H
    push Not at H
    have := IsUltrametricDist.norm_add_le_max μ μ⁻¹
    rw [hμ] at this
    linarith [max_le H.1 H.2]
  rcases key with h1 | h1
  · exact reduce s t hts (aleph0_lt_mk_padicAlgCl p) μ h1
      (aeval_iff_of_minpoly t htQ _ (by rw [hμ]; exact hr'))
  · exact reduce s t hts (aleph0_lt_mk_padicAlgCl p) μ⁻¹ h1
      (aeval_iff_of_minpoly t htQ _ (by rw [inv_inv, add_comm, hμ]; exact hr'))

/-- Tits: an embedding of the entry field into a normed field where `t` is the trace of
a proximal element. -/
theorem exists_ringHom_proximal (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (hinf : ∀ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → (t : ℂ) ≠ z + z⁻¹) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  by_cases h1 : Transcendental ℤ t
  · exact case_transcendental s t hts h1
  have halg : IsAlgebraic ℤ t := not_not.1 h1
  by_cases h2 : IsIntegral ℤ t
  · exact case_integral s t hts h2 hinf
  · exact case_nonintegral s t hts halg h2

end TitsLemma

end
end

section
open TitsLemma

theorem solution (s : Finset ℝ) (t : ℝ) (hts : t ∈ Subfield.closure (s : Set ℝ))
    (hinf : ∀ z : ℂ, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → (t : ℂ) ≠ z + z⁻¹) :
    ∃ (L : Type) (_ : NormedField L) (σ : Subfield.closure (s : Set ℝ) →+* L) (μ : L),
      1 < ‖μ‖ ∧ μ + μ⁻¹ = σ ⟨t, hts⟩ := by
  apply TitsLemma.exists_ringHom_proximal <;> assumption

end
