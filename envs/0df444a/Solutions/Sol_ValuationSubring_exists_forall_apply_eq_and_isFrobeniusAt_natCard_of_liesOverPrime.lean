-- Prove2me | solution 1 for ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ac5aad3c-c6f9-5587-a086-44efc15139d9

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ValuationSubring_exists_algEquiv_residue_pow_eq_of_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped Pointwise
open IsLocalRing

namespace PressFrobLift

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (q d : ℕ)

def goodSet (L : IntermediateField ↥K (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) :=
  {σ | ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A ↔ σ x ∈ A) ∧
        ∀ (hxA : x ∈ A) (hσ : σ x ∈ A), residue ↥A ⟨σ x, hσ⟩ = residue ↥A ⟨x, hxA⟩ ^ (q ^ d)}

theorem goodSet_anti {L L' : IntermediateField ↥K (AlgebraicClosure ℚ)} (h : L ≤ L') :
    goodSet K A q d L' ⊆ goodSet K A q d L := fun _ hσ x hx => hσ x (h hx)

theorem mul_mem_goodSet {L : IntermediateField ↥K (AlgebraicClosure ℚ)} {σ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ}
    (hσ : σ ∈ goodSet K A q d L) {τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ} (hτ : τ ∈ L.fixingSubgroup) :
    σ * τ ∈ goodSet K A q d L := by
  intro x hx
  have hτx : τ x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x hx
  have e : (σ * τ) x = σ x := by rw [AlgEquiv.mul_apply, hτx]
  obtain ⟨h1, h2⟩ := hσ x hx
  refine ⟨by rw [e]; exact h1, fun hxA hσ' => ?_⟩
  have hσ'' : σ x ∈ A := by rw [← e]; exact hσ'
  rw [← h2 hxA hσ'']
  congr 1
  exact Subtype.ext e

theorem isOpen_goodSet (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K ↥L] :
    IsOpen (goodSet K A q d L) := by
  rw [isOpen_iff_mem_nhds]
  intro σ hσ

  have hopen : IsOpen ((fun τ => σ * τ) '' (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ))) :=
    (Homeomorph.mulLeft σ).isOpenMap _ (IntermediateField.fixingSubgroup_isOpen L)
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨1, L.fixingSubgroup.one_mem, mul_one σ⟩) ?_
  rintro _ ⟨τ, hτ, rfl⟩
  exact mul_mem_goodSet K A q d hσ hτ

theorem isClosed_goodSet (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K ↥L] :
    IsClosed (goodSet K A q d L) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hopen : IsOpen ((fun τ => σ * τ) '' (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ))) :=
    (Homeomorph.mulLeft σ).isOpenMap _ (IntermediateField.fixingSubgroup_isOpen L)
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨1, L.fixingSubgroup.one_mem, mul_one σ⟩) ?_
  rintro _ ⟨τ, hτ, rfl⟩ hgood
  apply hσ
  have := mul_mem_goodSet K A q d hgood (L.fixingSubgroup.inv_mem hτ)
  rwa [mul_assoc, mul_inv_cancel, mul_one] at this

end PressFrobLift

namespace PressFrobLift

theorem pow_pow_mul_eq_self {R : Type*} [Monoid R] {a : R} {q m : ℕ} (h : a ^ (q ^ m) = a) (k : ℕ) :
    a ^ (q ^ (m * k)) = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem residue_pow_factorial_eq (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A) :
    IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ (Module.finrank ℚ ↥K).factorial) = IsLocalRing.residue ↥A ⟨x, hxA⟩ := by
  classical
  have hq : q.Prime := Fact.out
  letI : Algebra (ZMod q) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ q

  let xK : ↥K := ⟨x, hxK⟩
  have hint : IsIntegral ℚ xK := IsIntegral.of_finite ℚ xK
  have hp0 : minpoly ℚ xK ≠ 0 := minpoly.ne_zero hint
  have hpdeg : (minpoly ℚ xK).natDegree ≤ Module.finrank ℚ ↥K := minpoly.natDegree_le xK
  have hpx : Polynomial.aeval x (minpoly ℚ xK) = 0 := by
    have h := minpoly.aeval ℚ xK
    have h2 : Polynomial.aeval ((xK : ↥K) : AlgebraicClosure ℚ) (minpoly ℚ xK) =
        ((Polynomial.aeval xK (minpoly ℚ xK) : ↥K) : AlgebraicClosure ℚ) :=
      IntermediateField.aeval_coe K xK _
    rw [h, ZeroMemClass.coe_zero] at h2
    exact h2

  set f₀ : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ xK) with hf₀
  have hf₀x : Polynomial.aeval x f₀ = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ xK) hpx
  have hf₀0 : f₀ ≠ 0 := fun h0 => hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl (minpoly ℚ xK)).mp h0)
  have hf₀deg : f₀.natDegree ≤ (minpoly ℚ xK).natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hf₀, IsLocalization.integerNormalization_coeff]
    exact IsLocalization.coeffIntegerNormalization_of_coeff_zero _ _ i
      (Polynomial.coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hi))
  set f : Polynomial ℤ := f₀.primPart with hf
  have hfprim : f.IsPrimitive := Polynomial.isPrimitive_primPart f₀
  have hfx : Polynomial.aeval x f = 0 := by
    have hc0 : f₀.content ≠ 0 := fun h => hf₀0 (Polynomial.content_eq_zero_iff.mp h)
    have h1 : Polynomial.aeval x f₀ = ((f₀.content : ℤ) : AlgebraicClosure ℚ) * Polynomial.aeval x f := by
      conv_lhs => rw [Polynomial.eq_C_content_mul_primPart f₀]
      rw [map_mul, Polynomial.aeval_C, ← hf]
      rfl
    rw [hf₀x] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd (by exact_mod_cast h : f₀.content = 0) hc0
    · exact h
  have hfdeg : f.natDegree ≤ Module.finrank ℚ ↥K := by
    rw [hf, Polynomial.natDegree_primPart]
    exact hf₀deg.trans hpdeg

  set a : ↥A := ⟨x, hxA⟩ with ha
  have hfa : Polynomial.eval₂ (Int.castRingHom ↥A) a f = 0 := by
    have h1 : A.subtype (Polynomial.eval₂ (Int.castRingHom ↥A) a f) = 0 := by
      rw [Polynomial.hom_eval₂, RingHom.ext_int (A.subtype.comp (Int.castRingHom ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
      exact hfx
    exact Subtype.val_injective h1
  have hres : Polynomial.eval₂ (Int.castRingHom (IsLocalRing.ResidueField ↥A)) (IsLocalRing.residue ↥A a) f = 0 := by
    rw [← RingHom.ext_int ((IsLocalRing.residue ↥A).comp (Int.castRingHom ↥A)) (Int.castRingHom _), ← Polynomial.hom_eval₂,
      hfa, map_zero]
  set g : Polynomial (ZMod q) := f.map (Int.castRingHom (ZMod q)) with hg
  have hgx : Polynomial.aeval (IsLocalRing.residue ↥A a) g = 0 := by
    rw [Polynomial.aeval_def, hg, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod q) (IsLocalRing.ResidueField ↥A)).comp (Int.castRingHom (ZMod q))) (Int.castRingHom _)]
    exact hres
  have hg0 : g ≠ 0 := by
    intro h0
    have hall : ∀ i, (q : ℤ) ∣ f.coeff i := by
      intro i
      have := congrArg (fun r : Polynomial (ZMod q) => r.coeff i) h0
      simp only [hg, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp this
    have hC : Polynomial.C (q : ℤ) ∣ f := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hall
    have hu := hfprim (q : ℤ) hC
    rw [Int.isUnit_iff] at hu
    have h2 := hq.two_le
    omega
  have hgdeg : g.natDegree ≤ Module.finrank ℚ ↥K := (Polynomial.natDegree_map_le).trans hfdeg

  have halg : IsAlgebraic (ZMod q) (IsLocalRing.residue ↥A a) := ⟨g, hg0, hgx⟩
  have hxint : IsIntegral (ZMod q) (IsLocalRing.residue ↥A a) := halg.isIntegral
  have hmn : (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree ≤ Module.finrank ℚ ↥K := by
    have h1 := minpoly.degree_le_of_ne_zero (ZMod q) (IsLocalRing.residue ↥A a) hg0 hgx
    exact (Polynomial.natDegree_le_natDegree h1).trans hgdeg
  have hm0 : 0 < (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree := minpoly.natDegree_pos hxint
  let E := IntermediateField.adjoin (ZMod q) ({IsLocalRing.residue ↥A a} : Set (IsLocalRing.ResidueField ↥A))
  haveI : FiniteDimensional (ZMod q) ↥E := IntermediateField.adjoin.finiteDimensional hxint
  have hEr : Module.finrank (ZMod q) ↥E = (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree :=
    IntermediateField.adjoin.finrank hxint
  haveI : Finite ↥E := Module.finite_of_finite (ZMod q)
  letI : Fintype ↥E := Fintype.ofFinite ↥E
  have hcardE : Fintype.card ↥E = q ^ (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod q) (V := ↥E), ZMod.card, hEr]
  have hxE : IsLocalRing.residue ↥A a ∈ E := IntermediateField.mem_adjoin_simple_self (ZMod q) _
  have hpowE : (⟨_, hxE⟩ : ↥E) ^ (q ^ (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree) = ⟨_, hxE⟩ := by
    rw [← hcardE]; exact FiniteField.pow_card _
  have hpow' : IsLocalRing.residue ↥A a ^ (q ^ (minpoly (ZMod q) (IsLocalRing.residue ↥A a)).natDegree) =
      IsLocalRing.residue ↥A a := by
    have := congrArg (fun z : ↥E => (z : IsLocalRing.ResidueField ↥A)) hpowE
    simpa using this
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hm0 hmn
  rw [hk]
  exact pow_pow_mul_eq_self hpow' k

theorem residue_image_card (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ d : ℕ, 0 < d ∧
      Nat.card (Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1) = q ^ d ∧
      ∀ (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A),
        IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ d) = IsLocalRing.residue ↥A ⟨x, hxA⟩ := by
  classical
  have hq : q.Prime := Fact.out
  haveI : CharP (IsLocalRing.ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  set k₀ : Set (IsLocalRing.ResidueField ↥A) :=
    Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1 with hk₀
  have hfin : k₀.Finite := by
    have hne : (Polynomial.X ^ (q ^ (Module.finrank ℚ ↥K).factorial) - Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥A)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow (Nat.factorial_pos _).ne' hq.one_lt)
    refine Set.Finite.subset (Finset.finite_toSet
      (Polynomial.X ^ (q ^ (Module.finrank ℚ ↥K).factorial) - Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥A)).roots.toFinset) ?_
    rintro _ ⟨b, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    exact residue_pow_factorial_eq q A K b.1 b.2 b.1.2

  let T : Subring (IsLocalRing.ResidueField ↥A) :=
    { carrier := k₀
      zero_mem' := ⟨⟨0, zero_mem K⟩, by simp⟩
      one_mem' := ⟨⟨1, one_mem K⟩, by simp⟩
      add_mem' := by
        rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
        exact ⟨⟨b.1 + c.1, by push_cast; exact add_mem b.2 c.2⟩, by simp⟩
      neg_mem' := by
        rintro _ ⟨b, rfl⟩
        exact ⟨⟨-b.1, by push_cast; exact neg_mem b.2⟩, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
        exact ⟨⟨b.1 * c.1, by push_cast; exact mul_mem b.2 c.2⟩, by simp⟩ }
  haveI : Finite ↥T := hfin.to_subtype
  letI : Fintype ↥T := Fintype.ofFinite ↥T
  letI : Field ↥T := Fintype.fieldOfDomain ↥T
  haveI : CharP ↥T q := by
    refine ⟨fun n => ?_⟩
    rw [← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q n]
    constructor
    · intro h
      have := congrArg (Subtype.val) h
      simpa using this
    · intro h
      apply Subtype.ext
      simpa using h
  obtain ⟨d, -, hcardT⟩ := FiniteField.card ↥T q
  refine ⟨d, d.pos, ?_, fun x hxK hxA => ?_⟩
  · rw [← hcardT, ← Nat.card_eq_fintype_card]
    rfl
  · have hmem : IsLocalRing.residue ↥A ⟨x, hxA⟩ ∈ T := ⟨⟨⟨x, hxA⟩, hxK⟩, rfl⟩
    have h1 := FiniteField.pow_card (⟨_, hmem⟩ : ↥T)
    rw [hcardT] at h1
    have := congrArg (fun z : ↥T => (z : IsLocalRing.ResidueField ↥A)) h1
    simpa using this

end PressFrobLift

open PressFrobLift in
theorem solution_core
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] (d : ℕ)
    (hfix : ∀ (x : AlgebraicClosure ℚ) (hxK : x ∈ K) (hxA : x ∈ A),
      IsLocalRing.residue ↥A ⟨x, hxA⟩ ^ (q ^ d) = IsLocalRing.residue ↥A ⟨x, hxA⟩) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ z ∈ K, σ z = z) ∧ A.IsFrobeniusAt σ (q ^ d) := by
  classical
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
  haveI : Normal ℚ (AlgebraicClosure ℚ) :=
    normal_iff.mpr fun x => ⟨(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral, IsAlgClosed.splits _⟩
  haveI : Normal (↥K) (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ (↥K) (AlgebraicClosure ℚ)
  haveI : IsGalois (↥K) (AlgebraicClosure ℚ) := ⟨⟩

  let ι := {L : IntermediateField ↥K (AlgebraicClosure ℚ) // FiniteDimensional ↥K ↥L ∧ Normal ↥K ↥L}
  haveI : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  let t : ι → Set (AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ) := fun L => goodSet K A q d L.1

  have hne : ∀ L : ι, (t L).Nonempty := by
    intro L
    haveI : FiniteDimensional ↥K ↥L.1 := L.2.1
    haveI : Normal ↥K ↥L.1 := L.2.2
    obtain ⟨δ, hδA, hδres⟩ := ValuationSubring.exists_algEquiv_residue_pow_eq_of_nonunits K A (Fact.out) hA L.1 d hfix
    refine ⟨δ.symm, fun x hx => ?_⟩
    have hyL : δ.symm x ∈ L.1 :=
      (IntermediateField.normal_iff_forall_map_le'.mp L.2.2) δ.symm ⟨x, hx, rfl⟩
    have h1 := hδA (δ.symm x) hyL
    rw [AlgEquiv.apply_symm_apply] at h1
    refine ⟨h1.symm, fun hxA hσ => ?_⟩
    have := hδres (δ.symm x) hyL hσ (by rw [AlgEquiv.apply_symm_apply]; exact hxA)
    rw [← this]
    exact congrArg (fun y : IsLocalRing.ResidueField ↥A => y ^ (q ^ d))
      (congrArg (IsLocalRing.residue ↥A) (Subtype.ext (AlgEquiv.apply_symm_apply δ x)))
  have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
    intro L L'
    refine ⟨⟨L.1 ⊔ L'.1, ?_, ?_⟩, goodSet_anti K A q d le_sup_left, goodSet_anti K A q d le_sup_right⟩
    · haveI := L.2.1; haveI := L'.2.1; exact IntermediateField.finiteDimensional_sup L.1 L'.1
    · haveI := L.2.2; haveI := L'.2.2; haveI := L.2.1; haveI := L'.2.1; infer_instance
  have hcl : ∀ L : ι, IsClosed (t L) := fun L => by haveI := L.2.1; exact isClosed_goodSet K A q d L.1
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun L => (hcl L).isCompact) hcl
  rw [Set.mem_iInter] at hσ

  have hlayer : ∀ x : AlgebraicClosure ℚ, ∃ L : ι, x ∈ L.1 := by
    intro x
    have hxi : IsIntegral (↥K) x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top
    haveI : FiniteDimensional (↥K) ↥(IntermediateField.adjoin (↥K) {x}) := IntermediateField.adjoin.finiteDimensional hxi
    refine ⟨⟨IntermediateField.normalClosure (↥K) ↥(IntermediateField.adjoin (↥K) {x}) (AlgebraicClosure ℚ), inferInstance, inferInstance⟩, ?_⟩
    exact IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self (↥K) x)
  refine ⟨σ.restrictScalars ℚ, fun z hz => σ.commutes ⟨z, hz⟩, ?_⟩

  have hσA : σ.restrictScalars ℚ ∈ A.decompositionSubgroup ℚ := by
    rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨L, hL⟩ := hlayer y
      exact ((hσ L y hL).1).mp hy
    · intro hx
      refine ⟨σ.symm x, ?_, by simp⟩
      obtain ⟨L, hL⟩ := hlayer (σ.symm x)
      have := (hσ L (σ.symm x) hL).1
      rw [AlgEquiv.apply_symm_apply] at this
      exact this.mpr hx
  refine ⟨hσA, fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  rw [← IsLocalRing.ResidueField.residue_smul]
  obtain ⟨L, hL⟩ := hlayer (a : AlgebraicClosure ℚ)
  have h2 := (hσ L a hL).2 a.2
  have hmem : σ a ∈ A := ((hσ L a hL).1).mp a.2
  rw [← h2 hmem]
  rfl

open PressFrobLift in
theorem solution
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ (d : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), 0 < d ∧
      Nat.card (Set.range fun a : {a : ↥A // (a : AlgebraicClosure ℚ) ∈ K} => IsLocalRing.residue ↥A a.1) = q ^ d ∧
      (∀ z ∈ K, σ z = z) ∧ A.IsFrobeniusAt σ (q ^ d) := by
  obtain ⟨d, hd, hcard, hfix⟩ := residue_image_card q A hA K
  obtain ⟨σ, hσK, hσA⟩ := solution_core q A hA K d hfix
  exact ⟨d, σ, hd, hcard, hσK, hσA⟩

end S_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime (solution)
