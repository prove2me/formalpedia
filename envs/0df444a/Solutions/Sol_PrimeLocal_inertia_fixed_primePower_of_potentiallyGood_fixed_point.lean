-- Prove2me | solution 1 for PrimeLocal.inertia_fixed_primePower_of_potentiallyGood_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T00:49:49.204692+00:00
-- url     : https://prove2.me/submissions/790541d9-0951-4d19-90ff-4a6959a7a9af

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
import Theorems.Thm_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
import Theorems.Thm_WeierstrassCurve_card_le_three_of_forall_heq_vcInvFun
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_one_heq
import Theorems.Thm_WeierstrassCurve_exists_inertia_equivariant_reduceHom_of_variableChange_eq_map
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
/-- A rational point of prime order at least five forces every inertia comparison
variable change on a good special fibre to be the identity. Prime-to-residue-characteristic
reduction injectivity then fixes all prime-power torsion. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime) (hqp : q ≠ p) (hj : ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y := by
  classical
  have rigidity {K : Type} [Field K] [DecidableEq K]
      (E : WeierstrassCurve.Affine (AlgebraicClosure ℚ)) (D : WeierstrassCurve K)
      (Q : E.Point) (p : ℕ) (hp5 : 5 ≤ p) (hQ : addOrderOf Q = p)
      (θ : E.Point →+ D.toAffine.Point)
      (hθ : ∀ x, p • x = 0 → θ x = 0 → x = 0)
      (β : VariableChange K) (hβ : β • D = D)
      (hfix : ∀ n : ℕ, HEq (Point.vcInvFun β D.toAffine (θ (n • Q))) (θ (n • Q))) : β = 1 := by
    classical
    have hQzero : p • Q = 0 := by rw [← hQ]; exact addOrderOf_nsmul_eq_zero Q
    have hinj : Function.Injective (fun i : Fin p => θ (i.val • Q)) := by
      intro i j hij
      have ht : p • (i.val • Q - j.val • Q) = 0 := by
        rw [nsmul_sub, smul_smul, smul_smul, Nat.mul_comm p i.val, Nat.mul_comm p j.val, ← smul_smul, ← smul_smul, hQzero]
        simp
      have hh : i.val • Q - j.val • Q = 0 := hθ _ ht (by simp [map_sub, hij])
      apply Fin.ext
      apply nsmul_injOn_Iio_addOrderOf (x := Q)
      · simpa [hQ] using i.isLt
      · simpa [hQ] using j.isLt
      · exact sub_eq_zero.mp hh
    by_cases h1 : β = 1
    · exact h1
    have hn : β ≠ (⟨-1, 0, -D.a₁, -D.a₃⟩ : VariableChange K) := by
      intro he
      have hh := hfix 1
      simp only [one_nsmul] at hh
      rw [he] at hh
      have hn := Point.vcInvFun_neg_heq_neg D (θ Q)
      have hz : θ (2 • Q) = 0 := by
        rw [map_nsmul, two_nsmul]
        exact neg_eq_iff_add_eq_zero.mp (eq_of_heq (hn.symm.trans hh))
      have ht : p • (2 • Q) = 0 := by rw [smul_smul, Nat.mul_comm, ← smul_smul, hQzero]; simp
      have htwo := hθ _ ht hz
      have heq : (2 : ℕ) = 0 := nsmul_injOn_Iio_addOrderOf (x := Q)
        (by simp only [Set.mem_Iio, hQ]; omega)
        (by simp only [Set.mem_Iio, hQ]; omega) (by simpa using htwo)
      omega
    let F : Finset D.toAffine.Point := Finset.univ.image (fun i : Fin p => θ (i.val • Q))
    have hcard : F.card = p := by rw [Finset.card_image_of_injective _ hinj]; simp
    have hF : ∀ P ∈ F, HEq (Point.vcInvFun β D.toAffine P) P := by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
      exact hfix i.val
    have hc := WeierstrassCurve.card_le_three_of_forall_heq_vcInvFun D β hβ h1 hn F hF
    omega
  have jint (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (q : ℕ) [Fact q.Prime]
      (hj : (q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
      let E := W.map (Int.castRingHom ℚ)
      ∃ hE : E.IsElliptic, algebraMap ℚ (AlgebraicClosure ℚ) (@WeierstrassCurve.j _ _ E hE) ∈ A := by
    classical
    let E := W.map (Int.castRingHom ℚ)
    have hEΔ : E.Δ ≠ 0 := by simpa [E] using (Int.cast_ne_zero.mpr hΔ : (W.Δ : ℚ) ≠ 0)
    letI : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hEΔ⟩
    refine ⟨inferInstance, ?_⟩
    apply (A.algebraMap_rat_mem_iff_of_liesOverPrime hA E.j).mpr
    change (Rat.padicValuation q) E.j ≤ 1
    apply Rat.padicValuation_le_one_iff.mpr
    let Eq : WeierstrassCurve ℚ_[q] := W.map (Int.castRingHom ℚ_[q])
    have hEqΔ : Eq.Δ ≠ 0 := by
      dsimp only [Eq]
      rw [map_Δ]
      change (W.Δ : ℚ_[q]) ≠ 0
      exact_mod_cast hΔ
    letI : Eq.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hEqΔ⟩
    have hΔnorm : ‖(W.Δ : ℚ_[q])‖ = (q : ℝ) ^ (-(padicValInt q W.Δ : ℤ)) := by
      rw [show (W.Δ : ℚ_[q]) = ((W.Δ : ℚ) : ℚ_[q]) by norm_cast,
        Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hΔ), padicValRat.of_int]
      push_cast
      rfl
    have hjprod : Eq.j * Eq.Δ = Eq.c₄ ^ 3 := by
      conv_lhs => rw [← Eq.coe_Δ', WeierstrassCurve.j]
      rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have hle : ‖Eq.j‖ ≤ 1 := by
      have hle : ‖((W.c₄ ^ 3 : ℤ) : ℚ_[q])‖ ≤ (q : ℝ) ^ (-(padicValInt q W.Δ : ℤ)) :=
        (Padic.norm_int_le_pow_iff_dvd _ _).mpr hj
      rw [← hΔnorm] at hle
      have hle' : ‖Eq.j‖ * ‖Eq.Δ‖ ≤ ‖Eq.Δ‖ := by
        rw [← norm_mul, hjprod]
        simpa [Eq] using hle
      nlinarith [norm_pos_iff.mpr hEqΔ]
    have hmap : Eq.j = algebraMap ℚ ℚ_[q] E.j := by
      have hm : (algebraMap ℚ ℚ_[q]).comp (Int.castRingHom ℚ) = Int.castRingHom ℚ_[q] := by ext; simp
      simpa [Eq, E, WeierstrassCurve.map_map, hm] using E.map_j (algebraMap ℚ ℚ_[q])
    have hnorm : ‖(E.j : ℚ_[q])‖ ≤ 1 := by rwa [hmap] at hle
    have hu := PadicInt.isUnit_den E.j hnorm
    intro hd
    have hd' : (q : ℤ) ∣ (E.j.den : ℤ) := by exact_mod_cast hd
    have hn := (PadicInt.norm_int_lt_one_iff_dvd (p := q) (E.j.den : ℤ)).mpr hd'
    have he : ‖(E.j.den : ℤ_[q])‖ = 1 := PadicInt.isUnit_iff.mp hu
    norm_cast at hn
    rw [he] at hn
    exact lt_irrefl _ hn
  have goodmodel (E : WeierstrassCurve ℚ) [E.IsElliptic] (q : ℕ) (hq : q.Prime)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
      (hj : algebraMap ℚ (AlgebraicClosure ℚ) E.j ∈ A) :
      ∃ (D : WeierstrassCurve A) (κ : VariableChange (AlgebraicClosure ℚ)),
        κ • E.baseChange (AlgebraicClosure ℚ) = D.map A.subtype ∧ IsUnit D.Δ := by
    classical
    letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    let T : IntermediateField ℚ (AlgebraicClosure ℚ) := ⊤
    let e : T ≃ₐ[ℚ] AlgebraicClosure ℚ := IntermediateField.topEquiv
    let A' : ValuationSubring T := A.comap e.toRingEquiv.toRingHom
    let f : A' →+* A :=
      { toFun := fun x => ⟨e x, x.property⟩
        map_zero' := Subtype.ext (map_zero e)
        map_one' := Subtype.ext (map_one e)
        map_add' := fun x y => Subtype.ext (map_add e (x : T) (y : T))
        map_mul' := fun x y => Subtype.ext (map_mul e (x : T) (y : T)) }
    let g : A →+* A' :=
      { toFun := fun x => ⟨e.symm x, by simpa [A'] using x.property⟩
        map_zero' := Subtype.ext (map_zero e.symm)
        map_one' := Subtype.ext (map_one e.symm)
        map_add' := fun x y => Subtype.ext (map_add e.symm (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ))
        map_mul' := fun x y => Subtype.ext (map_mul e.symm (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ)) }
    have hj' : algebraMap ℚ T E.j ∈ A' := by
      change e (algebraMap ℚ T E.j) ∈ A
      simpa using hj
    have hu (n : ℕ) (hn : n.Coprime q) (hn0 : n ≠ 0) : IsUnit (n : A) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨(n : AlgebraicClosure ℚ)⁻¹, A.inv_natCast_mem_of_coprime_of_liesOverPrime hA hn⟩, ?_⟩
      apply Subtype.ext
      change (n : AlgebraicClosure ℚ) * (n : AlgebraicClosure ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn0)
    have hex : ∃ (D : WeierstrassCurve A') (κ : VariableChange T),
        κ • E.baseChange T = D.map A'.subtype ∧ IsUnit D.Δ := by
      by_cases hq2 : q = 2
      · have h3 : IsUnit (3 : A') := by
          simpa only [map_ofNat, map_natCast, Nat.cast_ofNat] using (hu 3 (by rw [hq2]; norm_num) (by norm_num)).map g
        obtain ⟨S, _, _, hS⟩ := E.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
          (Ω := AlgebraicClosure ℚ) (by norm_num)
        obtain ⟨D, κ, hκ, hD, _⟩ := hS T le_top A' h3 hj'
        exact ⟨D, κ, hκ, hD⟩
      · have h2 : IsUnit (2 : A') := by
          have hc : Nat.Coprime 2 q := (Nat.prime_two.coprime_iff_not_dvd).mpr
            (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm)
          simpa only [map_ofNat, map_natCast, Nat.cast_ofNat] using (hu 2 hc (by norm_num)).map g
        obtain ⟨S, _, _, hS⟩ := E.exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
          (Ω := AlgebraicClosure ℚ) (by norm_num)
        obtain ⟨D, κ, hκ, hD, _⟩ := hS T le_top A' h2 hj'
        exact ⟨D, κ, hκ, hD⟩
    obtain ⟨D, κ, hκ, hD⟩ := hex
    refine ⟨D.map f, κ.map e.toRingEquiv.toRingHom, ?_, ?_⟩
    · have hh := congrArg (fun V : WeierstrassCurve T => V.map e.toRingEquiv.toRingHom) hκ
      rw [← map_variableChange, WeierstrassCurve.map_map] at hh
      have hleft : (E.baseChange T).map e.toRingEquiv.toRingHom = E.baseChange (AlgebraicClosure ℚ) := by
        simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
        congr 1
      have hright : e.toRingEquiv.toRingHom.comp A'.subtype = A.subtype.comp f := by rfl
      rw [hleft, hright] at hh
      simpa only [WeierstrassCurve.map_map] using hh
    · rw [map_Δ]
      exact hD.map f
  letI : Fact q.Prime := ⟨hq⟩
  intro A hA τ hτ n y hy
  let E := W.map (Int.castRingHom ℚ)
  obtain ⟨hE, hjA⟩ := jint W hΔ q hj A hA
  letI : E.IsElliptic := hE
  obtain ⟨D, κ, hκ, hD⟩ := goodmodel E q hq A hA hjA
  letI : CharP (IsLocalRing.ResidueField A) q := A.residueField_charP_of_liesOverPrime hq hA
  have hpn : ∀ m : ℕ, ((p ^ m : ℕ) : IsLocalRing.ResidueField A) ≠ 0 := by
    intro m
    rw [Nat.cast_pow]
    apply pow_ne_zero
    intro hz
    have hdiv := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q p).mp hz
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv)
  obtain ⟨θ, g, _, hθ, hcomm, _⟩ :=
    E.exists_inertia_equivariant_reduceHom_of_variableChange_eq_map A D κ hκ hD
  obtain ⟨σ, hσ, rfl⟩ := hτ
  obtain ⟨_, hβ, heq⟩ := hcomm σ.val σ.property hσ
  have hθp : ∀ z, p • z = 0 → θ z = 0 → z = 0 := by
    intro z hz hzero
    apply hθ p z
    · simpa using hpn 1
    · exact hz
    · exact hzero
  have hfix : ∀ k : ℕ,
      HEq (Point.vcInvFun ((g σ.val).map (IsLocalRing.residue A))
        (D.map (IsLocalRing.residue A)).toAffine (θ (k • Q))) (θ (k • Q)) := by
    intro k
    have hh := heq (k • Q)
    rw [(Point.map σ.val.toAlgHom).map_nsmul] at hh
    change HEq _ (θ (k • (σ.val • Q))) at hh
    rwa [hQfix σ.val] at hh
  have hβone := rigidity (E.baseChange (AlgebraicClosure ℚ)).toAffine
    (D.map (IsLocalRing.residue A)) Q p hp5 hQord θ hθp
    ((g σ.val).map (IsLocalRing.residue A)) hβ hfix
  have hh := heq y
  rw [hβone] at hh
  have hsame : θ (Point.map σ.val.toAlgHom y) = θ y :=
    (eq_of_heq ((Point.vcInvFun_one_heq _ _).symm.trans hh)).symm
  have hz : θ (Point.map σ.val.toAlgHom y - y) = 0 := by
    rw [map_sub, hsame, sub_self]
  have hkill : p ^ n • (Point.map σ.val.toAlgHom y - y) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hy, _root_.map_zero, sub_self]
  exact sub_eq_zero.mp (hθ (p ^ n) _ (hpn n) hkill hz)
end PrimeLocal
