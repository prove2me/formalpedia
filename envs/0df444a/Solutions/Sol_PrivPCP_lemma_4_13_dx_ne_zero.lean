-- Prove2me | solution 1 for PrivPCP.lemma_4_13_dx_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:00:29.144593+00:00
-- url     : https://prove2.me/submissions/1210c689-748c-4313-aaf2-abc68bc9890a

import Mathlib


namespace PrivPCP.DX

open MvPolynomial

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

abbrev D2 (L : Type) [Field L] := TrivSqZeroExt L L

lemma aeval_tsze (v w : Fin 2 → L) (p : MvPolynomial (Fin 2) K) :
    aeval (fun i => (TrivSqZeroExt.inl (v i) + TrivSqZeroExt.inr (w i) : D2 L)) p =
      TrivSqZeroExt.inl (aeval v p) + TrivSqZeroExt.inr (∑ i, aeval v (pderiv i p) * w i) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C]
    simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero, TrivSqZeroExt.inr_zero, add_zero,
      aeval_C]
    rfl
  | add p r hp hr =>
    rw [map_add, hp, hr]
    ext <;> simp [Finset.sum_add_distrib, add_mul] <;> ring
  | mul_X p i hp =>
    rw [map_mul, hp, aeval_X]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add, Derivation.leibniz, map_add, map_mul, aeval_X, smul_eq_mul,
        pderiv_X, TrivSqZeroExt.snd_inl, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      fin_cases i <;> simp [Pi.single_apply] <;> ring

lemma pderiv_ne_zero (F : MvPolynomial (Fin 2) K) (i : Fin 2) (h : 0 < F.degreeOf i)
    (hc : ((F.degreeOf i : ℕ) : K) ≠ 0) : pderiv i F ≠ 0 := by
  have hF : F ≠ 0 := by rintro rfl; simp at h
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.2 hF) (fun m => m i)
  have hdeg : F.degreeOf i = m i := by rw [degreeOf_eq_sup, hmax]
  intro h0
  have := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
  rw [h0, coeff_zero] at this
  have hmi : 1 ≤ m i := by omega
  have e : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  rw [e] at this
  have e2 : (((m - Finsupp.single i 1 : Fin 2 →₀ ℕ) i : ℕ) : K) + 1 = ((m i : ℕ) : K) := by
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    rw [Nat.cast_sub hmi]; ring
  rw [e2, ← hdeg] at this
  exact (mul_ne_zero (mem_support_iff.1 hm) hc) this.symm

lemma degreeOf_pderiv_lt (F : MvPolynomial (Fin 2) K) (i : Fin 2) (h : 0 < F.degreeOf i) :
    (pderiv i F).degreeOf i < F.degreeOf i := by
  rw [degreeOf_lt_iff h]
  intro m hm
  rw [mem_support_iff, coeff_pderiv] at hm
  have hm' : m + Finsupp.single i 1 ∈ F.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
  have := (degreeOf_le_iff.mp (le_refl (F.degreeOf i))) _ hm'
  simp at this
  omega

lemma not_dvd_pderiv (F : MvPolynomial (Fin 2) K) (i : Fin 2) (h : 0 < F.degreeOf i)
    (hc : ((F.degreeOf i : ℕ) : K) ≠ 0) : ¬ F ∣ pderiv i F := by
  rintro ⟨G, hG⟩
  have hp := pderiv_ne_zero F i h hc
  have hF : F ≠ 0 := by rintro rfl; simp at h
  have hG0 : G ≠ 0 := by rintro rfl; rw [mul_zero] at hG; exact hp hG
  have := degreeOf_mul_eq (n := i) hF hG0
  have := degreeOf_pderiv_lt F i h
  rw [hG] at this
  omega

end PrivPCP.DX


namespace PrivPCP.DX

open MvPolynomial

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

theorem exists_derivation (F : MvPolynomial (Fin 2) K) (x y : L)
    (hker : RingHom.ker (aeval (R := K) ![x, y]).toRingHom = Ideal.span {F})
    (hadj : IntermediateField.adjoin K {x, y} = ⊤) :
    ∃ d : Derivation K L L, d x = aeval ![x, y] (pderiv 1 F) ∧ d y = -aeval ![x, y] (pderiv 0 F) := by
  set v : Fin 2 → L := ![x, y] with hv
  set w : Fin 2 → L := ![aeval v (pderiv 1 F), -aeval v (pderiv 0 F)] with hw
  set ψ : MvPolynomial (Fin 2) K →ₐ[K] D2 L :=
    aeval (fun i => (TrivSqZeroExt.inl (v i) + TrivSqZeroExt.inr (w i) : D2 L)) with hψdef
  have hψ : ∀ p, ψ p = TrivSqZeroExt.inl (aeval v p) +
      TrivSqZeroExt.inr (∑ i, aeval v (pderiv i p) * w i) := fun p => aeval_tsze v w p
  have hFv : aeval v F = 0 := by
    have : F ∈ RingHom.ker (aeval (R := K) v).toRingHom := by rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hψF : ψ F = 0 := by
    rw [hψ, hFv, Fin.sum_univ_two]
    ext <;> simp [w] <;> ring
  have hkerψ : ∀ p, aeval v p = 0 → ψ p = 0 := by
    intro p hp
    have : p ∈ Ideal.span {F} := by rw [← hker, RingHom.mem_ker]; simpa using hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 this
    rw [map_mul, hψF, mul_zero]
  set A := (aeval (R := K) v).range with hA
  set f : MvPolynomial (Fin 2) K →ₐ[K] A := (aeval v).rangeRestrict with hfdef
  have hf : Function.Surjective f := AlgHom.rangeRestrict_surjective _
  have hfv : ∀ p, ((f p : A) : L) = aeval v p := fun p => rfl
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    have : ((f p : A) : L) = 0 := by
      have : f p = 0 := hp
      rw [this]; rfl
    rw [hfv] at this
    exact hkerψ p this
  let φA : A →+* D2 L := (f.toRingHom).liftOfRightInverse (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨ψ.toRingHom, hle⟩
  have hφA : ∀ p, φA (f p) = ψ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply _ _ (Function.rightInverse_surjInv hf) ⟨ψ.toRingHom, hle⟩ p
  have hfst : ∀ a : A, (φA a).fst = (a : L) := by
    intro a
    obtain ⟨p, rfl⟩ := hf a
    rw [hφA, hψ, hfv]; simp
  -- `L` is the fraction field of `A`
  have hAadj : Algebra.adjoin K ({x, y} : Set L) = A := by
    rw [hA, ← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext z; simp [v, Fin.exists_fin_two, eq_comm, or_comm]
  haveI : IsFractionRing A L := IsFractionRing.of_field A L (fun z => by
    have hz : z ∈ IntermediateField.adjoin K ({x, y} : Set L) := by rw [hadj]; trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
    rw [hAadj] at hr hs
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩)
  have hunit : ∀ a : nonZeroDivisors A, IsUnit (φA a) := by
    intro a
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hfst, isUnit_iff_ne_zero]
    intro h0
    have : (a : A) = 0 := Subtype.ext h0
    exact nonZeroDivisors.coe_ne_zero a this
  let φ : L →+* D2 L := IsLocalization.lift (M := nonZeroDivisors A) hunit
  have hφ : ∀ a : A, φ (algebraMap A L a) = φA a := fun a => IsLocalization.lift_eq hunit a
  have hφfst : ∀ z : L, (φ z).fst = z := by
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp φ = RingHom.id L := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors A)
      ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        TrivSqZeroExt.fstHom_apply, RingHom.id_apply, hφ, hfst]
      rfl
    intro z
    have := congrArg (fun g => g z) this
    simpa using this
  have hφK : ∀ c : K, (φ (algebraMap K L c)).snd = 0 := by
    intro c
    have : algebraMap K L c = algebraMap A L (f (C c)) := by
      rw [IsScalarTower.algebraMap_apply K A L]
      congr 1
      rw [← MvPolynomial.algebraMap_eq, f.commutes]
    rw [this, hφ, hφA, hψ]
    simp
  let dl : L →ₗ[K] L :=
    { toFun := fun z => (φ z).snd
      map_add' := fun a b => by simp
      map_smul' := fun c z => by
        rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, hφK, hφfst, hφfst]
        simp [Algebra.smul_def] }
  let d : Derivation K L L := Derivation.mk' dl (fun a b => by
    show (φ (a * b)).snd = a • (φ b).snd + b • (φ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hφfst, hφfst]
    simp [smul_eq_mul]; ring)
  have hx : x = algebraMap A L (f (X 0)) := by
    show x = ((f (X 0) : A) : L); rw [hfv]; simp [v]
  have hy : y = algebraMap A L (f (X 1)) := by
    show y = ((f (X 1) : A) : L); rw [hfv]; simp [v]
  refine ⟨d, ?_, ?_⟩
  · show (φ x).snd = _
    rw [hx, hφ, hφA, hψ]
    simp [Fin.sum_univ_two, pderiv_X, w]
  · show (φ y).snd = _
    rw [hy, hφ, hφA, hψ]
    simp [Fin.sum_univ_two, pderiv_X, w]

end PrivPCP.DX


open PrivPCP.DX MvPolynomial in
theorem solution : ∀ (q : ℕ) [Fact q.Prime]
    (F : MvPolynomial (Fin 2) (AlgebraicClosure (ZMod q))),
    Irreducible F → 0 < F.degreeOf 0 → 0 < F.degreeOf 1 → F.degreeOf 0 < q → F.degreeOf 1 < q →
    ∀ (L : Type) [Field L] [Algebra (AlgebraicClosure (ZMod q)) L] (x y : L),
    RingHom.ker (MvPolynomial.aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom =
      Ideal.span {F} →
    IntermediateField.adjoin (AlgebraicClosure (ZMod q)) {x, y} = ⊤ →
    KaehlerDifferential.D (AlgebraicClosure (ZMod q)) L x ≠ 0 ∧
      KaehlerDifferential.D (AlgebraicClosure (ZMod q)) L y ≠ 0 := by
  intro q _ F hF hF0 hF1 haq hbq L _ _ x y hker hadj
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  obtain ⟨d, hdx, hdy⟩ := exists_derivation F x y hker hadj
  have hcast : ∀ i : Fin 2, 0 < F.degreeOf i → F.degreeOf i < q →
      ((F.degreeOf i : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := by
    intro i h0 hq h
    rw [CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q] at h
    have := Nat.le_of_dvd h0 h
    omega
  have hne : ∀ i : Fin 2, 0 < F.degreeOf i → F.degreeOf i < q →
      aeval (R := AlgebraicClosure (ZMod q)) ![x, y] (pderiv i F) ≠ 0 := by
    intro i h0 hq h
    have hm : pderiv i F ∈ RingHom.ker (aeval (R := AlgebraicClosure (ZMod q)) ![x, y]).toRingHom := by
      rw [RingHom.mem_ker]; exact h
    rw [hker, Ideal.mem_span_singleton] at hm
    exact not_dvd_pderiv F i h0 (hcast i h0 hq) hm
  constructor
  · intro h0
    have := d.liftKaehlerDifferential_comp_D x
    rw [h0, map_zero, hdx] at this
    exact hne 1 hF1 hbq this.symm
  · intro h0
    have := d.liftKaehlerDifferential_comp_D y
    rw [h0, map_zero, hdy, eq_comm, neg_eq_zero] at this
    exact hne 0 hF0 haq this


