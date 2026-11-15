-- Prove2me | solution 1 for PrimeLocal.no_fixed_prime_torsion_of_integral_j
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:16:18.080307+00:00
-- url     : https://prove2.me/submissions/778a0900-112b-46ac-bd0e-50f620be018c

import Mathlib
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero
import Theorems.Thm_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
import Theorems.Thm_WeierstrassCurve_exists_inertia_equivariant_reduceHom_of_variableChange_eq_map
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

open IsLocalRing ValuationSubring

namespace PrimeLocal
/-- Integral j and a fixed point of prime order force the nonzero cyclic reductions
to lie over at most q abscissas, contradicting the torsion size bound. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (hcount : 2 * q < p - 1) (hj : ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : False := by
  classical
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
  have exists_frobenius_abscissa_equation_goodModel {F : Type} {M : Type} [Field F] [Field M] [DecidableEq M] [Algebra F M] (A : ValuationSubring M) [DecidableEq (IsLocalRing.ResidueField A)] (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : WeierstrassCurve.VariableChange M) (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) {q : ℕ} (hfrob : ∀ z : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup F) • z = z ^ q) : ∃ a b : IsLocalRing.ResidueField A, a ≠ 0 ∧ ∀ (P : (E.baseChange M).toAffine.Point), WeierstrassCurve.Affine.Point.map (σ : M →ₐ[F] M) P = P → ∀ (x y : M) (hxy : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A), HEq (WeierstrassCurve.Affine.Point.vcInvFun κ (E.baseChange M).toAffine P) (WeierstrassCurve.Affine.Point.some x y hxy) → (IsLocalRing.residue A ⟨x, hx⟩) ^ q = a * IsLocalRing.residue A ⟨x, hx⟩ + b := by
    classical
    have coe_notMem_nonunits_of_isUnit {a : A} (ha : IsUnit a) : (a : M) ∉ A.nonunits := by
      rw [coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, not_not]
      exact ha
    
    have pow_mem_nonunits {a : M} (ha : a ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
        a ^ n ∈ A.nonunits := by
      induction n with
      | zero => exact absurd rfl hn
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simpa using ha
        · rw [pow_succ]
          exact A.nonunits.mul_mem (ih hpos.ne') ha
    
    have mem_of_sq_add_mul_eq {z b c : M} (hb : b ∈ A) (hc : c ∈ A) (h : z ^ 2 + b * z = c) :
        z ∈ A := by
      by_contra hz
      have hz0 : z ≠ 0 := fun h0 => hz (h0 ▸ A.zero_mem)
      have hzi : z⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hz
      have key : (1 : M) = c * (z⁻¹ * z⁻¹) - b * z⁻¹ := by
        field_simp
        linear_combination h
      refine A.one_notMem_nonunits ?_
      rw [key]
      exact A.nonunits.sub_mem (A.mul_mem_nonunits hc (A.nonunits.mul_mem hzi hzi))
        (A.mul_mem_nonunits hb hzi)
    
    have exists_map_subtype_eq_of_smul_eq (W W' : WeierstrassCurve A) (g : VariableChange M)
        (hg : g • W'.map A.subtype = W.map A.subtype) (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
        ∃ g₀ : VariableChange A, g₀.map A.subtype = g := by
      obtain ⟨gu, r, s, t⟩ := g
    
      set u : M := (gu : M) with hu_def
      have hu0 : u ≠ 0 := gu.ne_zero
      have huinv : ((gu⁻¹ : Mˣ) : M) = u⁻¹ := Units.val_inv_eq_inv_val gu
    
      have hΔ : ((W.Δ : A) : M) = u⁻¹ ^ 12 * ((W'.Δ : A) : M) := by
        have h := congrArg WeierstrassCurve.Δ hg
        rw [variableChange_Δ, map_Δ, map_Δ] at h
        dsimp only at h
        rw [huinv] at h
        exact h.symm
      have hΔW : ((W.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW
      have hΔW' : ((W'.Δ : A) : M) ∉ A.nonunits := coe_notMem_nonunits_of_isUnit hW'
    
      have hu : u ∈ A ∧ u⁻¹ ∈ A := by
        rcases A.mem_or_inv_mem u with huA | huA
        · refine ⟨huA, A.inv_mem_of_notMem_nonunits fun hun => hΔW' ?_⟩
          have h' : ((W'.Δ : A) : M) = ((W.Δ : A) : M) * u ^ 12 := by
            rw [hΔ]; field_simp
          rw [h']
          exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
        · refine ⟨?_, huA⟩
          have hun : u⁻¹ ∉ A.nonunits := fun hun => hΔW <| by
            rw [hΔ, mul_comm]
            exact A.mul_mem_nonunits (SetLike.coe_mem _) (pow_mem_nonunits hun (by norm_num))
          simpa using A.inv_mem_of_notMem_nonunits hun
      obtain ⟨huA, huiA⟩ := hu
    
      let u₀ : Aˣ := ⟨⟨u, huA⟩, ⟨u⁻¹, huiA⟩, Subtype.ext (mul_inv_cancel₀ hu0),
        Subtype.ext (inv_mul_cancel₀ hu0)⟩
    
      have h2A : (2 : M) ∈ A := by
        have : (2 : M) = ((2 : ℕ) : M) := by norm_num
        rw [this]; exact A.natCast_mem' 2
      have h3A : (3 : M) ∈ A := by
        have : (3 : M) = ((3 : ℕ) : M) := by norm_num
        rw [this]; exact A.natCast_mem' 3
    
      have ha₁ : (W'.map A.subtype).a₁ ∈ A := SetLike.coe_mem W'.a₁
      have ha₂ : (W'.map A.subtype).a₂ ∈ A := SetLike.coe_mem W'.a₂
      have ha₃ : (W'.map A.subtype).a₃ ∈ A := SetLike.coe_mem W'.a₃
      have ha₄ : (W'.map A.subtype).a₄ ∈ A := SetLike.coe_mem W'.a₄
      have ha₆ : (W'.map A.subtype).a₆ ∈ A := SetLike.coe_mem W'.a₆
      have hb₂ : (W'.map A.subtype).b₂ ∈ A := by rw [map_b₂]; exact SetLike.coe_mem _
      have hb₄ : (W'.map A.subtype).b₄ ∈ A := by rw [map_b₄]; exact SetLike.coe_mem _
      have hb₆ : (W'.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
      have hb₈ : (W'.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _
      have hB₂ : (W.map A.subtype).a₂ ∈ A := SetLike.coe_mem W.a₂
      have hB₆ : (W.map A.subtype).a₆ ∈ A := SetLike.coe_mem W.a₆
      have hBb₆ : (W.map A.subtype).b₆ ∈ A := by rw [map_b₆]; exact SetLike.coe_mem _
      have hBb₈ : (W.map A.subtype).b₈ ∈ A := by rw [map_b₈]; exact SetLike.coe_mem _
    
      have h6 : u ^ 6 * (W.map A.subtype).b₆ = (W'.map A.subtype).b₆
          + 2 * r * (W'.map A.subtype).b₄ + r ^ 2 * (W'.map A.subtype).b₂ + 4 * r ^ 3 := by
        have h := congrArg WeierstrassCurve.b₆ hg
        rw [variableChange_b₆] at h
        dsimp only at h
        rw [huinv] at h
        rw [← h]; field_simp
      have h8 : u ^ 8 * (W.map A.subtype).b₈ = (W'.map A.subtype).b₈
          + 3 * r * (W'.map A.subtype).b₆ + 3 * r ^ 2 * (W'.map A.subtype).b₄
          + r ^ 3 * (W'.map A.subtype).b₂ + 3 * r ^ 4 := by
        have h := congrArg WeierstrassCurve.b₈ hg
        rw [variableChange_b₈] at h
        dsimp only at h
        rw [huinv] at h
        rw [← h]; field_simp
      have hr : r ∈ A := by
        by_contra hrA
        have hr0 : r ≠ 0 := fun h0 => hrA (h0 ▸ A.zero_mem)
        have hri : r⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_of_notMem hrA
        have hri2 : r⁻¹ ^ 2 ∈ A.nonunits := pow_mem_nonunits hri two_ne_zero
        have hri3 : r⁻¹ ^ 3 ∈ A.nonunits := pow_mem_nonunits hri three_ne_zero
        have hri4 : r⁻¹ ^ 4 ∈ A.nonunits := pow_mem_nonunits hri four_ne_zero
    
        have h4 : (4 : M) =
            (u ^ 6 * (W.map A.subtype).b₆ - (W'.map A.subtype).b₆) * r⁻¹ ^ 3
              - 2 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2 - (W'.map A.subtype).b₂ * r⁻¹ := by
          rw [h6]; field_simp; ring
        have h4m : (4 : M) ∈ A.nonunits := by
          rw [h4]
          refine A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_
          · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 6) hBb₆) hb₆) hri3
          · exact A.mul_mem_nonunits (mul_mem h2A hb₄) hri2
          · exact A.mul_mem_nonunits hb₂ hri
    
        have h3 : (3 : M) =
            (u ^ 8 * (W.map A.subtype).b₈ - (W'.map A.subtype).b₈) * r⁻¹ ^ 4
              - 3 * (W'.map A.subtype).b₆ * r⁻¹ ^ 3 - 3 * (W'.map A.subtype).b₄ * r⁻¹ ^ 2
              - (W'.map A.subtype).b₂ * r⁻¹ := by
          rw [h8]; field_simp; ring
        have h3m : (3 : M) ∈ A.nonunits := by
          rw [h3]
          refine A.nonunits.sub_mem (A.nonunits.sub_mem (A.nonunits.sub_mem ?_ ?_) ?_) ?_
          · exact A.mul_mem_nonunits (sub_mem (mul_mem (pow_mem huA 8) hBb₈) hb₈) hri4
          · exact A.mul_mem_nonunits (mul_mem h3A hb₆) hri3
          · exact A.mul_mem_nonunits (mul_mem h3A hb₄) hri2
          · exact A.mul_mem_nonunits hb₂ hri
        refine A.one_notMem_nonunits ?_
        have h1 : (1 : M) = 4 - 3 := by norm_num
        rw [h1]
        exact A.nonunits.sub_mem h4m h3m
    
      have h2 : u ^ 2 * (W.map A.subtype).a₂ =
          (W'.map A.subtype).a₂ - s * (W'.map A.subtype).a₁ + 3 * r - s ^ 2 := by
        have h := congrArg WeierstrassCurve.a₂ hg
        rw [variableChange_a₂] at h
        dsimp only at h
        rw [huinv] at h
        rw [← h]; field_simp
      have hs : s ∈ A := by
        refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₁)
          (c := (W'.map A.subtype).a₂ + 3 * r - u ^ 2 * (W.map A.subtype).a₂) ha₁ ?_ ?_
        · exact sub_mem (add_mem ha₂ (mul_mem h3A hr)) (mul_mem (pow_mem huA 2) hB₂)
        · linear_combination h2
    
      have h6' : u ^ 6 * (W.map A.subtype).a₆ =
          (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
            + r ^ 3 - t * (W'.map A.subtype).a₃ - t ^ 2 - r * t * (W'.map A.subtype).a₁ := by
        have h := congrArg WeierstrassCurve.a₆ hg
        rw [variableChange_a₆] at h
        dsimp only at h
        rw [huinv] at h
        rw [← h]; field_simp
      have ht : t ∈ A := by
        refine mem_of_sq_add_mul_eq (b := (W'.map A.subtype).a₃ + r * (W'.map A.subtype).a₁)
          (c := (W'.map A.subtype).a₆ + r * (W'.map A.subtype).a₄ + r ^ 2 * (W'.map A.subtype).a₂
            + r ^ 3 - u ^ 6 * (W.map A.subtype).a₆) (add_mem ha₃ (mul_mem hr ha₁)) ?_ ?_
        · exact sub_mem (add_mem (add_mem (add_mem ha₆ (mul_mem hr ha₄))
            (mul_mem (pow_mem hr 2) ha₂)) (pow_mem hr 3)) (mul_mem (pow_mem huA 6) hB₆)
        · linear_combination h6'
    
      refine ⟨⟨u₀, ⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩, ?_⟩
      ext <;> rfl
    let d : A →+* A := MulSemiringAction.toRingHom (A.decompositionSubgroup F) A ⟨σ, hσ⟩
    let W' := W.map d
    have hd : A.subtype.comp d = (σ : M →+* M).comp A.subtype := by
      ext z
      rfl
    have hW' : W'.map A.subtype = (W.map A.subtype).map (σ : M →+* M) := by
      dsimp only [W']
      rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hd]
    have hg : (κ * (κ.map (σ : M →+* M))⁻¹) • W'.map A.subtype = W.map A.subtype := by
      have h1 : W'.map A.subtype = κ.map (σ : M →+* M) • E.baseChange M := by
        rw [hW', ← hκ, ← map_variableChange]
        exact congrArg (fun V => κ.map (σ : M →+* M) • V) (E.map_baseChange (σ : M →ₐ[F] M))
      rw [h1, ← mul_smul, inv_mul_cancel_right, hκ]
    have hΔ' : IsUnit W'.Δ := by
      dsimp only [W']
      rw [map_Δ]
      exact hΔ.map d
    obtain ⟨g, hg⟩ := exists_map_subtype_eq_of_smul_eq W W' _ hg hΔ hΔ'
    let a : IsLocalRing.ResidueField A := IsLocalRing.residue A (g.u : A) ^ 2
    let b : IsLocalRing.ResidueField A := IsLocalRing.residue A g.r
    refine ⟨a, b, pow_ne_zero 2 (Units.ne_zero (g.u.map (IsLocalRing.residue A).toMonoidHom)), ?_⟩
    intro P hP x y hxy hx hpoint
    have heq : (κ • E.baseChange M).toAffine = (W.map A.subtype).toAffine := congrArg _ hκ
    have hcoord : ∀ {V V' : WeierstrassCurve.Affine M} (hV : V = V')
        {x₁ y₁ x₂ y₂ : M} {h₁ : V.Nonsingular x₁ y₁} {h₂ : V'.Nonsingular x₂ y₂},
        HEq (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂) → x₁ = x₂ := by
      intro V V' hV x₁ y₁ x₂ y₂ h₁ h₂ h
      subst hV
      exact (Point.some.inj (eq_of_heq h)).1
    have hzero : ∀ {V V' : WeierstrassCurve.Affine M} (hV : V = V')
        {z w : M} {h : V'.Nonsingular z w}, HEq (0 : V.Point) (Point.some z w h) → False := by
      intro V V' hV z w h hz
      subst hV
      exact Point.some_ne_zero _ (eq_of_heq hz).symm
    have hmul : ∀ (C C' : VariableChange M) (z : M),
        vcXInv (C * C') z = vcXInv C (vcXInv C' z) := by
      intro C C' z
      have hu := C.u.ne_zero
      have hu' := C'.u.ne_zero
      simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
      field_simp
      ring
    have hmap : ∀ z : M, σ (vcXInv κ z) = vcXInv (κ.map (σ : M →+* M)) (σ z) := by
      intro z
      simp only [vcXInv, VariableChange.map, Units.coe_map_inv, map_mul, map_pow, map_sub]
      rfl
    have hσx : σ x = (g.u : A) ^ 2 * x + (g.r : M) := by
      cases P with
      | zero =>
        dsimp only [Point.vcInvFun] at hpoint
        exact False.elim (hzero heq hpoint)
      | some px py hp =>
        have hpx : σ px = px := by
          rw [Point.map_some] at hP
          exact (Point.some.inj hP).1
        have hx' : vcXInv κ px = x := hcoord heq hpoint
        have hfac : κ = g.map A.subtype * κ.map (σ : M →+* M) := by
          rw [hg, inv_mul_cancel_right]
        have key : vcXInv κ (σ px) = vcXInv (g.map A.subtype) (σ (vcXInv κ px)) := by
          conv_lhs => rw [hfac]
          rw [hmul, hmap]
        rw [hpx, hx'] at key
        have key' := congrArg (vcX (g.map A.subtype)) key
        rw [vcX_vcXInv] at key'
        exact key'.symm
    have hA : d ⟨x, hx⟩ = (g.u : A) ^ 2 * ⟨x, hx⟩ + g.r := Subtype.ext hσx
    have hres := congrArg (IsLocalRing.residue A) hA
    have hact : (⟨σ, hσ⟩ : A.decompositionSubgroup F) • IsLocalRing.residue A ⟨x, hx⟩ =
        IsLocalRing.residue A (d ⟨x, hx⟩) := by
      rfl
    rw [← hact, hfrob] at hres
    simpa only [map_add, map_mul, map_pow] using hres

  have card_points_over_fixed_abscissas_le_two_mul {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (S : Finset F) (T : Finset W.toAffine.Point) (hT : ∀ P ∈ T, ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = WeierstrassCurve.Affine.Point.some x y h ∧ x ∈ S) : T.card ≤ 2 * S.card  := by
    classical
    have hmaps : ∀ P ∈ T, P.xRep 0 ∈ S := by
      intro P hP
      obtain ⟨x, y, h, rfl, hx⟩ := hT P hP
      exact hx
    have hfiber : ∀ x ∈ S, (T.filter (fun P => P.xRep 0 = x)).card ≤ 2 := by
      intro x hx
      by_cases hempty : (T.filter (fun P => P.xRep 0 = x)).Nonempty
      · obtain ⟨Q, hQ⟩ := hempty
        have hsub : T.filter (fun P => P.xRep 0 = x) ⊆ {Q, -Q} := by
          intro P hP
          obtain ⟨hPT, hPx⟩ := Finset.mem_filter.mp hP
          obtain ⟨hQT, hQx⟩ := Finset.mem_filter.mp hQ
          have heq : P.xRep = Q.xRep := by
            obtain ⟨px, py, hp, rfl, _⟩ := hT P hPT
            obtain ⟨qx, qy, hq, rfl, _⟩ := hT Q hQT
            have hpq : px = qx := hPx.trans hQx.symm
            simp only [Point.xRep_some, hpq]
          simpa only [Finset.mem_insert, Finset.mem_singleton] using
            Point.eq_or_eq_neg_of_xRep_eq_xRep heq
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
        simp
    calc
      T.card = ∑ x ∈ S, (T.filter (fun P => P.xRep 0 = x)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _x ∈ S, 2 := Finset.sum_le_sum hfiber
      _ = 2 * S.card := by simp [Nat.mul_comm]
  letI : Fact q.Prime := ⟨hq⟩
  let E := W.map (Int.castRingHom ℚ)
  obtain ⟨A, hA, σ, hfrob⟩ := ValuationSubring.exists_isFrobeniusAt_rat q hq
  obtain ⟨hE, hjA⟩ := jint W hΔ q hj A hA
  letI : E.IsElliptic := hE
  obtain ⟨D, κ, hκ, hD⟩ := goodmodel E q hq A hA hjA
  let K := IsLocalRing.ResidueField A
  let Dr := D.map (IsLocalRing.residue A)
  letI : CharP K q := A.residueField_charP_of_liesOverPrime hq hA
  have hpK : (p : K) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff K q p).mp hz
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
  have hDr : Dr.Δ ≠ 0 := by
    dsimp only [Dr]
    rw [map_Δ]
    exact (hD.map (IsLocalRing.residue A)).ne_zero
  obtain ⟨θ, _, hrepr, hθ, _, _⟩ :=
    E.exists_inertia_equivariant_reduceHom_of_variableChange_eq_map A D κ hκ hD
  obtain ⟨a, b, ha, hab⟩ := exists_frobenius_abscissa_equation_goodModel A E D κ hκ hD
    σ hfrob.mem_decompositionSubgroup hfrob.smul_residue_eq
  have hQzero : p • Q = 0 := by rw [← hQord]; exact addOrderOf_nsmul_eq_zero Q
  have hinj : Function.Injective (fun i : Fin p => θ (i.val • Q)) := by
    intro i j hij
    have ht : p • (i.val • Q - j.val • Q) = 0 := by
      rw [nsmul_sub, smul_smul, smul_smul, Nat.mul_comm p i.val, Nat.mul_comm p j.val,
        ← smul_smul, ← smul_smul, hQzero]
      simp
    have hh : i.val • Q - j.val • Q = 0 := hθ p _ hpK ht (by simp [map_sub, hij])
    apply Fin.ext
    exact nsmul_injOn_Iio_addOrderOf (x := Q)
      (by simpa [hQord] using i.isLt) (by simpa [hQord] using j.isLt) (sub_eq_zero.mp hh)
  letI : NeZero p := ⟨hp.ne_zero⟩
  let T : Finset Dr.toAffine.Point :=
    (Finset.univ.erase (0 : Fin p)).image (fun i : Fin p => θ (i.val • Q))
  have hTcard : T.card = p - 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  let f : Polynomial K := Polynomial.X ^ q - (Polynomial.C a * Polynomial.X + Polynomial.C b)
  have hsmall : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
    · simp
  have hfdeg : f.natDegree = q := by
    dsimp only [f]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    apply lt_of_le_of_lt hsmall
    rw [Polynomial.natDegree_X_pow]
    have := hq.two_le
    omega
  have hfne : f ≠ 0 := by
    intro hz
    have := hfdeg
    rw [hz, Polynomial.natDegree_zero] at this
    exact hq.ne_zero this.symm
  let S := f.roots.toFinset
  have hScard : S.card ≤ q := by
    exact (Multiset.toFinset_card_le _).trans (hfdeg ▸ Polynomial.card_roots' f)
  have hT : ∀ P ∈ T, ∃ (x y : K) (h : Dr.toAffine.Nonsingular x y),
      P = Point.some x y h ∧ x ∈ S := by
    intro P hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hnzero : θ (i.val • Q) ≠ 0 := by
      intro hz
      apply hi0
      apply hinj
      simpa using hz
    obtain ⟨V, hV, hred⟩ := hrepr hDr (i.val • Q)
    cases V with
    | zero =>
      have hz : θ (i.val • Q) = 0 := by
        change θ (i.val • Q) = WeierstrassCurve.reducePoint hDr (0 : _) at hred
        simpa only [WeierstrassCurve.reducePoint_zero] using hred
      exact (hnzero hz).elim
    | some x y hxy =>
      by_cases hx : x ∈ A
      · have heq := hab (i.val • Q) (by
          rw [map_nsmul]
          exact congrArg (fun R => i.val • R) (hQfix σ)) x y hxy hx hV
        rw [show WeierstrassCurve.reduceHom hDr (Point.some x y hxy) =
          WeierstrassCurve.reducePoint hDr (Point.some x y hxy) from rfl,
          WeierstrassCurve.reducePoint_some_of_mem hDr hxy hx] at hred
        refine ⟨_, _, _, hred, ?_⟩
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots hfne).mpr
        change Polynomial.eval _ f = 0
        simpa [f, sub_eq_zero] using heq
      · apply (hnzero ?_).elim
        simpa only [WeierstrassCurve.reduceHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          WeierstrassCurve.reducePoint_some_of_notMem hDr hxy hx] using hred
  have hc := card_points_over_fixed_abscissas_le_two_mul Dr S T hT
  omega
end PrimeLocal
