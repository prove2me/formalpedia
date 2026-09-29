-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9beefb69-1dc9-58e0-83ae-6ed24bc575e7

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun
import Theorems.Thm_ModularCurve_IsGamma0PowAt_zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped Classical

namespace RawToModuliAux

theorem exists_coprime_nsmul_eq_of_mem_zmultiples {G : Type} [AddCommGroup G] (a b : G) (M : ℕ) [NeZero M]
    (ha : addOrderOf a = M) (hb : addOrderOf b = M) (hbmem : b ∈ AddSubgroup.zmultiples a) :
    ∃ k : ℕ, k.Coprime M ∧ b = k • a := by
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hbmem
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  set k : ℕ := (m % (M : ℤ)).toNat with hkdef
  have hkint : (k : ℤ) = m % (M : ℤ) := by rw [hkdef]; exact Int.toNat_of_nonneg (Int.emod_nonneg m hM0)
  have hMa : (M : ℤ) • a = 0 := by rw [natCast_zsmul, ← ha, addOrderOf_nsmul_eq_zero]
  have hk : k • a = m • a := by
    rw [← natCast_zsmul, hkint]
    conv_rhs => rw [← Int.emod_add_mul_ediv m (M : ℤ), add_zsmul, mul_comm, mul_zsmul, hMa, zsmul_zero, add_zero]
  refine ⟨k, ?_, hk.symm⟩
  by_cases hk0 : k = 0
  ·
    have : M = 1 := by rw [← hb, ← hk, hk0, zero_nsmul, addOrderOf_zero]
    rw [hk0, this]
    exact Nat.coprime_one_right 0
  · have hord : addOrderOf (k • a) = M := by rw [hk, hb]
    rw [addOrderOf_nsmul' a hk0, ha] at hord
    have hg : Nat.gcd M k = 1 := by
      rcases (Nat.div_eq_self).mp hord with h | h
      · exact absurd h (NeZero.ne M)
      · exact h
    exact Nat.Coprime.symm hg

theorem mem_zmultiples_of_nsmul_mem {G : Type} [AddCommGroup G] (a b : G) (u v : ℕ) (huv : Nat.Coprime u v)
    (hu : u • b ∈ AddSubgroup.zmultiples a) (hv : v • b ∈ AddSubgroup.zmultiples a) :
    b ∈ AddSubgroup.zmultiples a := by
  obtain ⟨c, d, hcd⟩ := Nat.isCoprime_iff_coprime.mpr huv
  have : b = c • (u • b) + d • (v • b) := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_zsmul, hcd, one_zsmul]
  rw [this]
  exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hu c) (AddSubgroup.zsmul_mem _ hv d)

theorem zmultiples_eq_of_forall_primeFactors {G : Type} [AddCommGroup G] (M : ℕ) :
    ∀ (a b : G), M ≠ 0 → addOrderOf a = M → addOrderOf b = M →
      (∀ p ∈ M.primeFactors, AddSubgroup.zmultiples ((M / p ^ M.factorization p) • a) =
        AddSubgroup.zmultiples ((M / p ^ M.factorization p) • b)) →
      AddSubgroup.zmultiples a = AddSubgroup.zmultiples b := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro a b hM ha hb hprime
  by_cases hM1 : M = 1
  · subst hM1
    rw [AddMonoid.addOrderOf_eq_one_iff] at ha hb
    rw [ha, hb]

  obtain ⟨p, hp, hpM⟩ := Nat.exists_prime_and_dvd hM1
  have hpmem : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩
  have hsplit : ordProj[p] M * ordCompl[p] M = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hM₁0 : ordCompl[p] M ≠ 0 := (Nat.ordCompl_pos p hM).ne'
  have hk1 : 1 ≤ M.factorization p := (hp.dvd_iff_one_le_factorization hM).mp hpM
  have hproj2 : 2 ≤ ordProj[p] M :=
    le_trans hp.two_le (by simpa using Nat.pow_le_pow_right hp.pos hk1)
  have hP0 : ordProj[p] M ≠ 0 := by omega
  have hM₁lt : ordCompl[p] M < M := by
    have h1 : 1 * ordCompl[p] M < ordProj[p] M * ordCompl[p] M :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl (Nat.pos_of_ne_zero hM₁0)
    rwa [one_mul, hsplit] at h1
  have hcop : Nat.Coprime (ordProj[p] M) (ordCompl[p] M) := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hM)
  have hdvdP : ordProj[p] M ∣ M := Dvd.intro _ hsplit

  have horda : addOrderOf (ordProj[p] M • a) = ordCompl[p] M := by
    rw [addOrderOf_nsmul' a hP0, ha, Nat.gcd_eq_right hdvdP]
  have hordb : addOrderOf (ordProj[p] M • b) = ordCompl[p] M := by
    rw [addOrderOf_nsmul' b hP0, hb, Nat.gcd_eq_right hdvdP]

  have hIH : AddSubgroup.zmultiples (ordProj[p] M • a) = AddSubgroup.zmultiples (ordProj[p] M • b) := by
    refine ih (ordCompl[p] M) hM₁lt _ _ hM₁0 horda hordb ?_
    intro r hr
    have hrp : r ≠ p := by
      rintro rfl
      exact Nat.not_dvd_ordCompl hp hM (Nat.dvd_of_mem_primeFactors hr)
    have hfac : (ordCompl[p] M).factorization r = M.factorization r := by
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne hrp]
    have hrdvd : r ^ M.factorization r ∣ ordCompl[p] M := by rw [← hfac]; exact Nat.ordProj_dvd _ r
    have harith : ordCompl[p] M / r ^ (ordCompl[p] M).factorization r * ordProj[p] M = M / r ^ M.factorization r := by
      rw [hfac]
      calc ordCompl[p] M / r ^ M.factorization r * ordProj[p] M = ordProj[p] M * (ordCompl[p] M / r ^ M.factorization r) :=
            mul_comm _ _
        _ = ordProj[p] M * ordCompl[p] M / r ^ M.factorization r := (Nat.mul_div_assoc _ hrdvd).symm
        _ = M / r ^ M.factorization r := by rw [hsplit]
    rw [smul_smul, smul_smul, harith]
    exact hprime r (Nat.primeFactors_mono (Nat.ordCompl_dvd M p) hM hr)
  have hpk : AddSubgroup.zmultiples (ordCompl[p] M • a) = AddSubgroup.zmultiples (ordCompl[p] M • b) := hprime p hpmem

  have key : ∀ (a b : G), AddSubgroup.zmultiples (ordProj[p] M • a) = AddSubgroup.zmultiples (ordProj[p] M • b) →
      AddSubgroup.zmultiples (ordCompl[p] M • a) = AddSubgroup.zmultiples (ordCompl[p] M • b) →
      b ∈ AddSubgroup.zmultiples a := by
    intro a b h1 h2
    refine mem_zmultiples_of_nsmul_mem a b (ordProj[p] M) (ordCompl[p] M) hcop ?_ ?_
    · have hm : ordProj[p] M • b ∈ AddSubgroup.zmultiples (ordProj[p] M • a) := h1 ▸ AddSubgroup.mem_zmultiples _
      exact (AddSubgroup.zmultiples_le.mpr (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples a) _)) hm
    · have hm : ordCompl[p] M • b ∈ AddSubgroup.zmultiples (ordCompl[p] M • a) := h2 ▸ AddSubgroup.mem_zmultiples _
      exact (AddSubgroup.zmultiples_le.mpr (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples a) _)) hm
  exact le_antisymm (AddSubgroup.zmultiples_le.mpr (key b a hIH.symm hpk.symm))
    (AddSubgroup.zmultiples_le.mpr (key a b hIH hpk))

theorem monic_and_natDegree_le_of_isGamma0PowAt {T : Type} [CommRing T] (W : WeierstrassCurve T) (p k : ℕ)
    (h : Polynomial T) (hh : ModularCurve.IsGamma0PowAt W p k h) :
    h.Monic ∧ h.natDegree ≤ ModularCurve.gamma0PowDeg p k := by
  unfold ModularCurve.IsGamma0PowAt at hh
  unfold ModularCurve.gamma0PowDeg
  by_cases hpk : p ^ k = 2
  · rw [if_pos hpk] at hh ⊢; exact ⟨hh.monic, hh.natDegree_le⟩
  · rw [if_neg hpk] at hh ⊢; exact ⟨hh.monic, hh.natDegree_le⟩

end RawToModuliAux

open RawToModuliAux

theorem solution
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [NeZero M']
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)
    (κ : Type) [Field κ] [IsAlgClosed κ] [DecidableEq κ] [Algebra A κ] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (x x' : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw κ)
    (hxx' : (Quot.mk _ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt κ) = Quot.mk _ x')
    (g : (x.curve).toAffine.Point) (g' : (x'.curve).toAffine.Point)
    (hg : (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x.curve).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x.level.1 p).IsRoot x₁))
    (hg' : (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : (x'.curve).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (x'.level.1 p).IsRoot x₁)) :
    (Quot.mk _ (⟨x.curve, ⟨x.isUnit_Δ⟩, g, hg.1⟩ : ModularCurve.Gamma0Pair M' κ) : ModularCurve.ModuliPoint M' κ) =
      Quot.mk _ (⟨x'.curve, ⟨x'.isUnit_Δ⟩, g', hg'.1⟩ : ModularCurve.Gamma0Pair M' κ) := by
  classical

  have hequiv : Equivalence (ModularCurve.RigidWeierstrassData.Rel
      (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯) (T := κ)) :=
    ⟨fun y => ⟨1, ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_one y).symm⟩,
     fun {y z} h => by
       obtain ⟨C, hC⟩ := h
       exact ⟨C⁻¹, by rw [hC, ← (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_mul,
         inv_mul_cancel, (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_one]⟩,
     fun {y z w} h h' => by
       obtain ⟨C, hC⟩ := h
       obtain ⟨C', hC'⟩ := h'
       exact ⟨C' * C, by rw [hC', hC, (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_mul]⟩⟩
  obtain ⟨C, hC⟩ : ∃ C : WeierstrassCurve.VariableChange κ,
      x' = (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x :=
    hequiv.eqvGen_iff.mp (Quot.eqvGen_exact hxx')
  subst hC

  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hxl : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt x.curve (p : ℕ) (M'.factorization (p : ℕ)) (x.level.1 p) := x.isLevel.1.1
  have hxl' : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve (p : ℕ)
        (M'.factorization (p : ℕ)) (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).level.1 p) :=
    ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).isLevel.1.1
  have hmon := fun p : ↥M'.primeFactors => monic_and_natDegree_le_of_isGamma0PowAt x.curve _ _ _ (hxl p)
  let g'' : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve).toAffine.Point :=
    WeierstrassCurve.Affine.Point.vcInvFun C x.curve.toAffine g
  have hvc : WeierstrassCurve.Affine.Point.vcFun C x.curve.toAffine g'' = g :=
    (WeierstrassCurve.Affine.Point.vcFun_rightInverse (C := C) (W := x.curve.toAffine)) g
  have hcut'' : addOrderOf g'' = M' ∧
      ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ)
        (h₁ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve).toAffine.Nonsingular x₁ y₁),
        n • g'' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g'') = (p : ℕ) ^ M'.factorization (p : ℕ) →
        (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).level.1 p).IsRoot x₁ :=
    WeierstrassCurve.Affine.Point.cutOut_smul_of_cutOut_vcFun κ x.curve C M' (fun p => x.level.1 p)
      (fun p => (hmon p).1) (fun p => (hmon p).2) g'' (by rw [hvc]; exact hg)

  haveI : ((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve.IsElliptic :=
    ⟨((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).isUnit_Δ⟩
  have hprime : ∀ p ∈ M'.primeFactors,
      AddSubgroup.zmultiples ((M' / p ^ M'.factorization p) • g'') = AddSubgroup.zmultiples ((M' / p ^ M'.factorization p) • g') := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpdvd : p ∣ M' := Nat.dvd_of_mem_primeFactors hp
    have hpk : p ^ M'.factorization p ∣ M' := Nat.ordProj_dvd M' p
    have hk1 : 1 ≤ M'.factorization p := (hpp.dvd_iff_one_le_factorization hM0).mp hpdvd
    have hpk2 : 2 ≤ p ^ M'.factorization p :=
      le_trans hpp.two_le (by simpa using Nat.pow_le_pow_right hpp.pos hk1)
    have hn0 : M' / p ^ M'.factorization p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpk)
      (Nat.pos_of_ne_zero (by positivity))).ne'
    have hgcd : Nat.gcd M' (M' / p ^ M'.factorization p) = M' / p ^ M'.factorization p :=
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpk)
    have hpκ : ((p : ℕ) : κ) ≠ 0 := by
      intro hp0
      apply hM'κ
      rw [← Nat.mul_div_cancel' hpdvd, Nat.cast_mul, hp0, zero_mul]

    have horder : ∀ a : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve).toAffine.Point,
        addOrderOf a = M' → addOrderOf ((M' / p ^ M'.factorization p) • a) = p ^ M'.factorization p := by
      intro a ha
      rw [addOrderOf_nsmul' a hn0, ha, hgcd, Nat.div_div_self hpk hM0]
    have ho'' := horder g'' hcut''.1
    have ho' := horder g' hg'.1

    rcases hq'' : (M' / p ^ M'.factorization p) • g'' with _ | ⟨xa, ya, ha⟩
    · exfalso
      rw [hq''] at ho''
      have : addOrderOf (0 : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve).toAffine.Point) =
          p ^ M'.factorization p := ho''
      rw [addOrderOf_zero] at this
      omega
    rcases hq' : (M' / p ^ M'.factorization p) • g' with _ | ⟨xb, yb, hb⟩
    · exfalso
      rw [hq'] at ho'
      have : addOrderOf (0 : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C x).curve).toAffine.Point) =
          p ^ M'.factorization p := ho'
      rw [addOrderOf_zero] at this
      omega
    have hra := hcut''.2 ⟨p, hp⟩ _ xa ya ha hq'' ho''
    have hrb := hg'.2 ⟨p, hp⟩ _ xb yb hb hq' ho'
    rw [hq''] at ho''
    rw [hq'] at ho'
    exact ModularCurve.IsGamma0PowAt.zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq _ p (M'.factorization p) hpκ
      _ (hxl' ⟨p, hp⟩) xa ya xb yb ha hb ho'' ho' hra hrb

  have hzm : AddSubgroup.zmultiples g'' = AddSubgroup.zmultiples g' :=
    zmultiples_eq_of_forall_primeFactors M' g'' g' hM0 hcut''.1 hg'.1 hprime
  obtain ⟨k, hk, hgk⟩ := exists_coprime_nsmul_eq_of_mem_zmultiples g'' g' M' hcut''.1 hg'.1
    (hzm ▸ AddSubgroup.mem_zmultiples g')

  exact Quot.sound ⟨C, rfl, k, hk, heq_of_eq hgk⟩

end S_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_moduliPoint_mk_eq_of_quot_mk_eq_of_raw_rigidDataH1Pow (solution)
