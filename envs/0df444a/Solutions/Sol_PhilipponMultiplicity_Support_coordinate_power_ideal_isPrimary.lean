-- Prove2me | solution 1 for PhilipponMultiplicity.Support.coordinate_power_ideal_isPrimary
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T12:53:42.337526+00:00
-- url     : https://prove2.me/submissions/b724839f-28ba-44bc-a65b-080738b74a5f

import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic


set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimarySupport

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primary_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (h : (⊥ : Ideal S).IsPrimary) : (⊥ : Ideal R).IsPrimary := by
  have heq : (⊥ : Ideal S).comap f = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact map_eq_zero_iff f hf
  rw [← heq]
  exact h.comap f

theorem primary_bot_quotient (Q : Ideal R) (hQ : Q.IsPrimary) :
    (⊥ : Ideal (R ⧸ Q)).IsPrimary := by
  haveI : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : a * b ∈ Q := by
    simpa only [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hxy
  rcases (Ideal.isPrimary_iff.mp hQ).2 hab with ha | hb
  · left
    simpa only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] using ha
  · right
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, by simpa only [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] using hn⟩

/-- McCoy's theorem makes zero-primaryness stable under adjoining one variable. -/
theorem primary_bot_polynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (Polynomial R)).IsPrimary := by
  haveI : Nontrivial R := nontrivial_of_ne (x := (0 : R)) (y := 1) (by
    intro h
    exact (Ideal.ne_top_iff_one _).mp hR.ne_top h.symm)
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro P Q hPQ
  by_cases hP : P = 0
  · exact Or.inl hP
  right
  have hQ : Q ∉ nonZeroDivisors (Polynomial R) := by
    intro hQ
    exact hP (hQ.2 P hPQ)
  obtain ⟨a, ha, h⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hQ
  have hnil : IsNilpotent Q := by
    apply Polynomial.isNilpotent_iff.mpr
    intro i
    have hzero : a * Q.coeff i = 0 := by
      simpa only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero] using
        congrArg (fun f : Polynomial R => f.coeff i) h
    have hm := ((Ideal.isPrimary_iff.mp hR).2 hzero).resolve_left ha
    exact hm
  exact hnil

/-- Polynomial extension in finitely many variables preserves a primary zero ideal. -/
theorem primary_bot_mvPolynomial {σ : Type*} [Finite σ]
    (hR : (⊥ : Ideal R).IsPrimary) : (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  classical
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ
  · intro α β _ e ih
    exact primary_bot_of_injective (MvPolynomial.renameEquiv R e.symm).toRingHom
      (MvPolynomial.renameEquiv R e.symm).injective ih
  · exact primary_bot_of_injective (MvPolynomial.isEmptyRingEquiv R PEmpty).toRingHom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).injective hR
  · intro α _ ih
    exact primary_bot_of_injective (MvPolynomial.optionEquivLeft R α).toRingHom
      (MvPolynomial.optionEquivLeft R α).injective (primary_bot_polynomial ih)
end PhilipponMultiplicity.PrimarySupport
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.CoordinatePowerSupport

variable (K : Type*) [Field K] (σ : Type*)

/-- The coordinate origin is the kernel of constant-coefficient evaluation. -/
theorem variable_ideal_eq_ker :
    idealOfVars σ K = RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  have hsub (f : MvPolynomial σ K) : f - C (constantCoeff f) ∈ idealOfVars σ K := by
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg =>
      convert (idealOfVars σ K).add_mem hf hg using 1 <;> simp only [map_add] <;> ring
    | mul_X f i hf =>
      simpa using (idealOfVars σ K).mul_mem_left f (Ideal.subset_span ⟨i,rfl⟩)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simp [RingHom.mem_ker]
  · intro f hf
    have hf0 : constantCoeff f = 0 := hf
    simpa [hf0] using hsub f

theorem variable_ideal_maximal : (idealOfVars σ K).IsMaximal := by
  rw [variable_ideal_eq_ker]
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  exact ⟨C a, constantCoeff_C σ a⟩

/-- Constraining every variable by a positive pure power gives a maximal radical. -/
theorem full_power_radical (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ n i)).radical =
      idealOfVars σ K := by
  apply le_antisymm
  · apply (variable_ideal_maximal K σ).isPrime.radical_le_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.pow_mem_of_mem (idealOfVars σ K)
      (show (X i : MvPolynomial σ K) ∈ idealOfVars σ K from Ideal.subset_span ⟨i,rfl⟩)
      (n i) (hn i)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨n i, Ideal.subset_span ⟨i,rfl⟩⟩

theorem full_power_primary (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ n i)).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [full_power_radical K σ n hn]
  exact variable_ideal_maximal K σ

/-- Polynomial extension of a primary ideal, using the coefficient quotient
kernel and the already proved multivariable McCoy argument. -/
theorem map_C_primary {R τ : Type*} [CommRing R] [Finite τ]
    (Q : Ideal R) (hQ : Q.IsPrimary) :
    (Q.map (C : R →+* MvPolynomial τ R)).IsPrimary := by
  have hzero := PrimarySupport.primary_bot_mvPolynomial (σ := τ)
    (PrimarySupport.primary_bot_quotient Q hQ)
  have hker := hzero.comap (MvPolynomial.map (Ideal.Quotient.mk Q))
  change (RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk Q) :
    MvPolynomial τ R →+* MvPolynomial τ (R ⧸ Q))).IsPrimary at hker
  rwa [MvPolynomial.ker_map, Ideal.mk_ker] at hker

/-- Split the unrestricted variables from the constrained coefficient variables. -/
def splitVariables (S : Set σ) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial (Sᶜ : Set σ) (MvPolynomial S K) := by
  classical
  let e : σ ≃ (Sᶜ : Set σ) ⊕ S :=
    (Equiv.Set.sumCompl S).symm.trans (Equiv.sumComm S (Sᶜ : Set σ))
  exact (renameEquiv K e).trans (sumAlgEquiv K (Sᶜ : Set σ) S)

theorem splitVariables_X_mem (S : Set σ) (i : S) :
    splitVariables K σ S (X i.val) = C (X i) := by
  classical
  simp [splitVariables, Equiv.Set.sumCompl_symm_apply]

theorem split_power_ideal (S : Set σ) (n : σ → ℕ) :
    (Ideal.span ((fun i => (X i : MvPolynomial σ K) ^ n i) '' S)).map
      (splitVariables K σ S).toRingHom =
    (Ideal.span (Set.range fun i : S => (X i : MvPolynomial S K) ^ n i.val)).map
      (C : MvPolynomial S K →+* MvPolynomial (Sᶜ : Set σ) (MvPolynomial S K)) := by
  classical
  rw [Ideal.map_span, Ideal.map_span]
  congr 1
  ext f
  constructor
  · rintro ⟨g,⟨i,hi,rfl⟩,rfl⟩
    refine ⟨(X (⟨i,hi⟩ : S) : MvPolynomial S K) ^ n i, ⟨⟨i,hi⟩,rfl⟩, ?_⟩
    simp only [map_pow]
    exact congrArg (fun f => f ^ n i) (splitVariables_X_mem K σ S ⟨i,hi⟩).symm
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    refine ⟨(X i.val : MvPolynomial σ K) ^ n i.val, ⟨i.val,i.property,rfl⟩, ?_⟩
    simp only [map_pow]
    exact congrArg (fun f => f ^ n i.val) (splitVariables_X_mem K σ S i)

theorem coordinate_power_primary [Finite σ]
    (S : Set σ) (n : σ → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    (Ideal.span ((fun i => (X i : MvPolynomial σ K) ^ n i) '' S)).IsPrimary := by
  classical
  let e := splitVariables K σ S
  let Q := Ideal.span (Set.range fun i : S => (X i : MvPolynomial S K) ^ n i.val)
  have hQ : Q.IsPrimary := full_power_primary K S (fun i => n i.val) (fun i => hn i.val i.property)
  have h := (map_C_primary (τ := (Sᶜ : Set σ)) Q hQ).comap e.toRingHom
  rw [← split_power_ideal K σ S n] at h
  rwa [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at h

end PhilipponMultiplicity.CoordinatePowerSupport

end

universe u v

theorem solution
    (K : Type u) [Field K] (σ : Type v) [Finite σ]
    (S : Set σ) (n : σ → ℕ) (hn : ∀ i ∈ S, 0 < n i) :
    (Ideal.span ((fun i => (MvPolynomial.X i : MvPolynomial σ K) ^ n i) '' S)).IsPrimary := by
  exact PhilipponMultiplicity.CoordinatePowerSupport.coordinate_power_primary K σ S n hn
