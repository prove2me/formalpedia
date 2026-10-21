-- Prove2me | solution 1 for SI.base_unit_inversions
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:14:12.515988+00:00
-- url     : https://prove2.me/submissions/475aea78-c0b6-47c8-a4e6-2cfdefdbf748

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

namespace SI
namespace G60

def invMat : Matrix (Fin 7) (Fin 7) ℤ :=
  !![-1, -1, 1, 1, 1, 0, 2;
     0, 1, -2, 0, 0, 0, 0;
     0, 0, 1, 0, 1, 0, 1;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 1]

lemma inv_left : invMat * constMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma inv_right : constMat * invMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem dim_bij : Function.Bijective dimOfExpo := by
  refine Function.bijective_iff_has_inverse.2 ⟨invMat.mulVec, fun v => ?_, fun v => ?_⟩
  · simp only [dimOfExpo, Matrix.mulVec_mulVec, inv_left, Matrix.one_mulVec]
  · simp only [dimOfExpo, Matrix.mulVec_mulVec, inv_right, Matrix.one_mulVec]

variable (M : SIModel)

lemma expo_neg (a : Dim) : M.expoOfDim (-a) = - M.expoOfDim a := by
  have h := M.expoOfDim_add a (-a)
  rw [add_neg_cancel, M.expoOfDim_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma expo_sub (a b : Dim) : M.expoOfDim (a - b) = M.expoOfDim a - M.expoOfDim b := by
  rw [sub_eq_add_neg, M.expoOfDim_add, expo_neg, sub_eq_add_neg]

lemma coef_neg (a : Dim) : M.coefOfDim (-a) = (M.coefOfDim a)⁻¹ := by
  have h := M.coefOfDim_mul a (-a)
  rw [add_neg_cancel, M.coefOfDim_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

lemma coef_sub (a b : Dim) : M.coefOfDim (a - b) = M.coefOfDim a / M.coefOfDim b := by
  rw [sub_eq_add_neg, M.coefOfDim_mul, coef_neg, div_eq_mul_inv]

-- abbreviations for the seven constant dimensions
lemma eT : dT = -(-dT) := by simp
lemma eL : dL = (dL - dT) + dT := by abel
lemma eM : dM = (dM + (dL + dL) - dT) - (dL - dT) - (dL - dT) + (-dT) := by abel
lemma eI : dI = (dI + dT) - dT := by abel
lemma eTh : dTh = (dM + (dL + dL) - dT) + (-dT) - (dM + (dL + dL) - (dT + dT) - dTh) := by abel
lemma eN : dN = -(-dN) := by simp
lemma eJ : dJ = (dJ - (dL + dL) - dM + (dT + dT + dT)) + (dM + (dL + dL) - dT) + (-dT) + (-dT) := by abel

lemma qext {a b : QMono} (h1 : a.coef = b.coef) (h2 : a.expo = b.expo) : a = b := by
  cases a; cases b; simp_all

theorem coef_dN (M : SIModel) : M.coefOfDim dN = (602214076 : ℚ) / (10 : ℚ) ^ 14 := by
  obtain ⟨hz1, hz2⟩ := M.hzValue
  obtain ⟨c1, c2⟩ := M.msValue
  obtain ⟨h1, h2⟩ := M.jsValue
  obtain ⟨e1, e2⟩ := M.coulValue
  obtain ⟨k1, k2⟩ := M.jkValue
  obtain ⟨n1, n2⟩ := M.molValue
  obtain ⟨l1, l2⟩ := M.lmwValue
  have cT : M.coefOfDim dT = 9192631770 := by rw [eT, coef_neg, hz2]; norm_num
  have xT : M.expoOfDim dT = -eC Const.dCs := by rw [eT, expo_neg, hz1]
  have cL : M.coefOfDim dL = 9192631770 / 299792458 := by
    rw [eL, M.coefOfDim_mul, c2, cT]; norm_num
  have xL : M.expoOfDim dL = eC Const.c - eC Const.dCs := by
    rw [eL, M.expoOfDim_add, c1, xT, sub_eq_add_neg]
  have cM : M.coefOfDim dM = (299792458 : ℚ) * (299792458 : ℚ) * (10 : ℚ) ^ 42 / (9192631770 * 662607015) := by
    rw [eM, M.coefOfDim_mul, coef_sub, coef_sub, h2, c2, hz2]; norm_num
  have xM : M.expoOfDim dM = eC Const.h + eC Const.dCs - (eC Const.c + eC Const.c) := by
    rw [eM, M.expoOfDim_add, expo_sub, expo_sub, h1, c1, hz1]; abel
  have cI : M.coefOfDim dI = (10 : ℚ) ^ 28 / (9192631770 * 1602176634) := by
    rw [eI, coef_sub, e2, cT]; norm_num
  have xI : M.expoOfDim dI = eC Const.dCs + eC Const.e := by
    rw [eI, expo_sub, e1, xT]; abel
  have cTh : M.coefOfDim dTh = (1380649 : ℚ) * (10 : ℚ) ^ 13 / (662607015 * 9192631770) := by
    rw [eTh, coef_sub, M.coefOfDim_mul, h2, hz2, k2]; norm_num
  have xTh : M.expoOfDim dTh = eC Const.dCs + eC Const.h - eC Const.kB := by
    rw [eTh, expo_sub, M.expoOfDim_add, h1, hz1, k1]; abel
  have cN : M.coefOfDim dN = (602214076 : ℚ) / (10 : ℚ) ^ 14 := by
    rw [eN, coef_neg, n2]; norm_num
  have xN : M.expoOfDim dN = -(eC Const.NA) := by rw [eN, expo_neg, n1]
  have cJ : M.coefOfDim dJ = (10 : ℚ) ^ 42 / (662607015 * (9192631770 : ℚ) ^ 2 * 683) := by
    rw [eJ, M.coefOfDim_mul, M.coefOfDim_mul, M.coefOfDim_mul, l2, h2, hz2]; norm_num
  have xJ : M.expoOfDim dJ = eC Const.dCs + eC Const.dCs + eC Const.h + eC Const.Kcd := by
    rw [eJ, M.expoOfDim_add, M.expoOfDim_add, M.expoOfDim_add, l1, h1, hz1]; abel
  exact cN

end G60
end SI

namespace SI
namespace G60

theorem approx :
    abs (mMono.coef - 30663319 / (10 : ℚ) ^ 6) < 1 / (10 : ℚ) ^ 6 ∧
    abs (kgMono.coef / (10 : ℚ) ^ 40 - 14755214 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 ∧
    abs (AMono.coef / (10 : ℚ) ^ 8 - 67896868 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 ∧
    abs (KMono.coef - 22666653 / (10 : ℚ) ^ 7) < 1 / (10 : ℚ) ^ 6 ∧
    abs (cdMono.coef / (10 : ℚ) ^ 10 - 26148305 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 := by
  simp only [mMono, kgMono, AMono, KMono, cdMono, abs_lt]
  norm_num

theorem ev (M : SIModel) :
    toQ M eVolt = qmul (⟨1, eC Const.e⟩ : QMono) (toQ M volt) := by
  obtain ⟨e1, e2⟩ := M.coulValue
  have hd : joule.dim = (dI + dT) + volt.dim := by ext i; fin_cases i <;> rfl
  have hv : volt.val = 1 := by
    norm_num [volt, watt, joule, newton, ampere, kilogram, metre, second, umul, udiv, uinv]
  have hj : joule.val = 1 := by
    norm_num [joule, newton, kilogram, metre, second, umul, udiv, uinv]
  apply qext
  · simp only [toQ, eVolt, uscale, qmul, hj, hv]
    rw [hd, M.coefOfDim_mul, e2, ← mul_assoc]
    norm_num
  · simp only [toQ, eVolt, uscale, qmul]
    rw [hd, M.expoOfDim_add, e1]

end G60
end SI

namespace SI
namespace G60

def w : Fin 7 → ℚ := ![1 / 9192631770, 1 / 299792458, (10 : ℚ) ^ 42 / 662607015,
  (10 : ℚ) ^ 28 / 1602176634, (10 : ℚ) ^ 29 / 1380649, (10 : ℚ) ^ 14 / 602214076, 1 / 683]

lemma w_ne (i : Fin 7) : w i ≠ 0 := by fin_cases i <;> norm_num [w]

def cf (d : Dim) : ℚ := ∏ i, w i ^ (invMat.mulVec d i)

lemma cf_eC (d : Dim) (k : Fin 7) (h : invMat.mulVec d = Pi.single k 1) : cf d = w k := by
  rw [cf, h, Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def model : SIModel where
  expoOfDim := invMat.mulVec
  coefOfDim := cf
  expoOfDim_zero := Matrix.mulVec_zero _
  expoOfDim_add a b := Matrix.mulVec_add _ _ _
  coefOfDim_one := by simp [cf]
  coefOfDim_mul a b := by
    simp only [cf, Matrix.mulVec_add, Pi.add_apply, zpow_add₀ (w_ne _), Finset.prod_mul_distrib]
  hzValue := by
    have h : invMat.mulVec (-dT) = Pi.single 0 1 := by ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 0 h]; rfl⟩
  msValue := by
    have h : invMat.mulVec (dL - dT) = Pi.single 1 1 := by ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 1 h]; rfl⟩
  jsValue := by
    have h : invMat.mulVec (dM + (dL + dL) - dT) = Pi.single 2 1 := by ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 2 h]; rfl⟩
  coulValue := by
    have h : invMat.mulVec (dI + dT) = Pi.single 3 1 := by ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 3 h]; rfl⟩
  jkValue := by
    have h : invMat.mulVec (dM + (dL + dL) - (dT + dT) - dTh) = Pi.single 4 1 := by
      ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 4 h]; rfl⟩
  molValue := by
    have h : invMat.mulVec (-dN) = Pi.single 5 1 := by ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 5 h]; rfl⟩
  lmwValue := by
    have h : invMat.mulVec (dJ - (dL + dL) - dM + (dT + dT + dT)) = Pi.single 6 1 := by
      ext i; fin_cases i <;> rfl
    refine ⟨by rw [h]; ext i; fin_cases i <;> rfl, by rw [cf_eC _ 6 h]; rfl⟩

theorem mole_wrong (M : SIModel) : toQ M mole ≠ molMono := by
  intro h
  have := congrArg QMono.coef h
  simp only [toQ, mole, molMono, one_mul, coef_dN] at this
  norm_num at this

end G60
end SI

namespace SI
namespace G60

def ehom (M : SIModel) : Dim →+ (Fin 7 → ℤ) := AddMonoidHom.mk' M.expoOfDim M.expoOfDim_add

lemma expo_dimOfExpo (M : SIModel) (v : Fin 7 → ℤ) : M.expoOfDim (dimOfExpo v) = v := by
  let g : (Fin 7 → ℤ) →+ (Fin 7 → ℤ) := (ehom M).comp constMat.mulVecLin.toAddMonoidHom
  have hg : g = AddMonoidHom.id _ := by
    refine AddMonoidHom.functions_ext _ _ _ (fun k x => ?_)
    have hx : (Pi.single k x : Fin 7 → ℤ) = x • Pi.single k 1 := by
      rw [← Pi.single_smul]; simp
    rw [hx, map_zsmul, map_zsmul]
    congr 1
    simp only [g, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Matrix.mulVecLin_apply, ehom, AddMonoidHom.mk'_apply, AddMonoidHom.id_apply]
    obtain ⟨hz1, -⟩ := M.hzValue
    obtain ⟨c1, -⟩ := M.msValue
    obtain ⟨h1, -⟩ := M.jsValue
    obtain ⟨e1, -⟩ := M.coulValue
    obtain ⟨k1, -⟩ := M.jkValue
    obtain ⟨n1, -⟩ := M.molValue
    obtain ⟨l1, -⟩ := M.lmwValue
    fin_cases k <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · have : constMat.mulVec (Pi.single 0 1) = -dT := by ext i; fin_cases i <;> rfl
      rw [this, hz1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 1 1) = dL - dT := by ext i; fin_cases i <;> rfl
      erw [this, c1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 2 1) = dM + (dL + dL) - dT := by ext i; fin_cases i <;> rfl
      erw [this, h1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 3 1) = dI + dT := by ext i; fin_cases i <;> rfl
      erw [this, e1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 4 1) = dM + (dL + dL) - (dT + dT) - dTh := by
        ext i; fin_cases i <;> rfl
      erw [this, k1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 5 1) = -dN := by ext i; fin_cases i <;> rfl
      erw [this, n1]; ext i; fin_cases i <;> rfl
    · have : constMat.mulVec (Pi.single 6 1) = dJ - (dL + dL) - dM + (dT + dT + dT) := by
        ext i; fin_cases i <;> rfl
      erw [this, l1]; ext i; fin_cases i <;> rfl
  have := congrArg (fun φ => φ v) hg
  simpa [g, ehom, dimOfExpo] using this

theorem faithful (M : SIModel)
    (hbas : Function.Bijective dimOfExpo) :
    ∀ u v : SIUnit, IsCoherent u → IsCoherent v →
      toQ M u = toQ M v → u = v := by
  intro u v hu hv h
  have hd : ∀ d : Dim, d = dimOfExpo (M.expoOfDim d) := by
    intro d
    obtain ⟨x, rfl⟩ := hbas.2 d
    rw [expo_dimOfExpo]
  have he := congrArg QMono.expo h
  simp only [toQ] at he
  obtain ⟨uv, ud⟩ := u
  obtain ⟨vv, vd⟩ := v
  simp only [IsCoherent] at hu hv
  simp only [SIUnit.mk.injEq]
  exact ⟨hu.trans hv.symm, by rw [hd ud, he, ← hd]⟩

end G60
end SI

open SI in
theorem solution : ¬ (∀ (M : SIModel),
    toQ M second = sMono ∧
    toQ M metre = mMono ∧
    toQ M kilogram = kgMono ∧
    toQ M ampere = AMono ∧
    toQ M kelvin = KMono ∧
    toQ M mole = molMono ∧
    toQ M candela = cdMono) :=
  by
  intro h
  exact SI.G60.mole_wrong _ (h SI.G60.model).2.2.2.2.2.1
