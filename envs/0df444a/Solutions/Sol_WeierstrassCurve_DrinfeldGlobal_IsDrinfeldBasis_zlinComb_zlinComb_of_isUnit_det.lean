-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/912d8e48-4d5b-537f-8d13-b048f584b398

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

namespace P2mKcDrinfeldRelabel

theorem zpow_eq_zpow_of_cast_eq {Γ : Type*} [Group Γ] {x : Γ} {q : ℕ} (hx : x ^ q = 1) {m n : ℤ}
    (h : (m : ZMod q) = (n : ZMod q)) : x ^ m = x ^ n := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub m n q).mp h
  have hn : n = m + (q : ℤ) * k := by linear_combination hk
  rw [hn, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, mul_one]

theorem combo_eq {Γ : Type*} [CommGroup Γ] (x y : Γ) (m₁ n₁ m₂ n₂ : ℤ) (a b : ℕ) :
    (x ^ m₁ * y ^ n₁) ^ a * (x ^ m₂ * y ^ n₂) ^ b =
      x ^ ((a : ℤ) * m₁ + (b : ℤ) * m₂) * y ^ ((a : ℤ) * n₁ + (b : ℤ) * n₂) := by
  rw [mul_pow, mul_pow, ← zpow_natCast (x ^ m₁) a, ← zpow_natCast (y ^ n₁) a,
    ← zpow_natCast (x ^ m₂) b, ← zpow_natCast (y ^ n₂) b, ← zpow_mul, ← zpow_mul, ← zpow_mul,
    ← zpow_mul, mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 2 <;> ring

section Index

variable (q : ℕ) [NeZero q]

def coord (i : Fin (q * q)) : ZMod q × ZMod q :=
  (((i.val / q : ℕ) : ZMod q), ((i.val % q : ℕ) : ZMod q))

omit [NeZero q] in
theorem div_lt (i : Fin (q * q)) : i.val / q < q :=
  Nat.div_lt_of_lt_mul i.isLt

theorem mod_lt' (i : Fin (q * q)) : i.val % q < q :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))

noncomputable def coordEquiv : Fin (q * q) ≃ ZMod q × ZMod q where
  toFun := coord q
  invFun z := finProdFinEquiv (⟨z.1.val, ZMod.val_lt _⟩, ⟨z.2.val, ZMod.val_lt _⟩)
  left_inv i := by
    have h1 : (⟨(((i.val / q : ℕ) : ZMod q)).val, ZMod.val_lt _⟩ : Fin q) = i.divNat := by
      apply Fin.ext
      rw [Fin.coe_divNat]
      exact ZMod.val_cast_of_lt (div_lt q i)
    have h2 : (⟨(((i.val % q : ℕ) : ZMod q)).val, ZMod.val_lt _⟩ : Fin q) = i.modNat := by
      apply Fin.ext
      rw [Fin.coe_modNat]
      exact ZMod.val_cast_of_lt (mod_lt' q i)
    show finProdFinEquiv (⟨(((i.val / q : ℕ) : ZMod q)).val, ZMod.val_lt _⟩,
      ⟨(((i.val % q : ℕ) : ZMod q)).val, ZMod.val_lt _⟩) = i
    rw [h1, h2]
    exact finProdFinEquiv.apply_symm_apply i
  right_inv z := by
    obtain ⟨z₁, z₂⟩ := z
    show coord q (finProdFinEquiv ((⟨z₁.val, ZMod.val_lt _⟩ : Fin q), (⟨z₂.val, ZMod.val_lt _⟩ : Fin q))) =
      (z₁, z₂)
    generalize hx : finProdFinEquiv ((⟨z₁.val, ZMod.val_lt _⟩ : Fin q), (⟨z₂.val, ZMod.val_lt _⟩ : Fin q)) = x
    have hsymm : finProdFinEquiv.symm x = ((⟨z₁.val, ZMod.val_lt _⟩ : Fin q), (⟨z₂.val, ZMod.val_lt _⟩ : Fin q)) := by
      rw [← hx, Equiv.symm_apply_apply]
    have hdiv : x.val / q = z₁.val := by
      have h' := congrArg (fun p : Fin q × Fin q => (p.1 : ℕ)) hsymm
      exact (Fin.coe_divNat x).symm.trans h'
    have hmod : x.val % q = z₂.val := by
      have h' := congrArg (fun p : Fin q × Fin q => (p.2 : ℕ)) hsymm
      exact (Fin.coe_modNat x).symm.trans h'
    simp only [coord, hdiv, hmod, ZMod.natCast_zmod_val]

@[scoped simp] theorem coordEquiv_apply (i : Fin (q * q)) : coordEquiv q i = coord q i := rfl

variable (g : Matrix (Fin 2) (Fin 2) ℤ)

def linMap (z : ZMod q × ZMod q) : ZMod q × ZMod q :=
  ((g 0 0 : ZMod q) * z.1 + (g 0 1 : ZMod q) * z.2, (g 1 0 : ZMod q) * z.1 + (g 1 1 : ZMod q) * z.2)

omit [NeZero q] in
theorem linMap_eq_mulVec (z : ZMod q × ZMod q) (k : Fin 2) :
    ((Int.castRingHom (ZMod q)).mapMatrix g).mulVec ![z.1, z.2] k = ![(linMap q g z).1, (linMap q g z).2] k := by
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, linMap, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem linMap_bijective (hg : IsUnit ((g.det : ℤ) : ZMod q)) : Function.Bijective (linMap q g) := by
  classical
  set M : Matrix (Fin 2) (Fin 2) (ZMod q) := (Int.castRingHom (ZMod q)).mapMatrix g with hM
  have hMu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hM, ← RingHom.map_det]
    exact hg
  have hsurj : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hMu
  have hbij : Function.Bijective M.mulVec := Finite.surjective_iff_bijective.mp hsurj
  refine Finite.injective_iff_bijective.mp fun z z' hzz' => ?_
  have hv : M.mulVec ![z.1, z.2] = M.mulVec ![z'.1, z'.2] := by
    funext k
    rw [linMap_eq_mulVec, linMap_eq_mulVec, hzz']
  have hv' := hbij.1 hv
  have h1 := congrFun hv' 0
  have h2 := congrFun hv' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  exact Prod.ext h1 h2

noncomputable def linEquiv (hg : IsUnit ((g.det : ℤ) : ZMod q)) : (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) :=
  Equiv.ofBijective (linMap q g) (linMap_bijective q g hg)

noncomputable def perm (hg : IsUnit ((g.det : ℤ) : ZMod q)) : Equiv.Perm (Fin (q * q)) :=
  (coordEquiv q).trans ((linEquiv q g hg).trans (coordEquiv q).symm)

theorem coord_perm (hg : IsUnit ((g.det : ℤ) : ZMod q)) (i : Fin (q * q)) :
    coord q (perm q g hg i) = linMap q g (coord q i) := by
  show coordEquiv q ((coordEquiv q).symm (linEquiv q g hg (coordEquiv q i))) = _
  rw [Equiv.apply_symm_apply]
  rfl

end Index

section Sections

variable {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}
  (G : RelativeGroupLaw T (projModelStrCR W))
  (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)

include hcomm

@[reducible] noncomputable def secGroup : CommGroup (Section W) :=
  { G.pointGroup (𝟙 _) with mul_comm := hcomm }

theorem nsmul_eq_pow (k : ℕ) (x : Section W) :
    letI := secGroup G hcomm; G.nsmul (𝟙 _) k x = x ^ k := by
  letI := secGroup G hcomm
  induction k with
  | zero => rfl
  | succ k ih =>
      show G.mul _ (G.nsmul _ k x) x = x ^ (k + 1)
      rw [ih, pow_succ]
      rfl

theorem zsmulSection_eq_zpow (n : ℤ) (x : Section W) :
    letI := secGroup G hcomm; ModularCurve.LevelRelabelling.zsmulSection G n x = x ^ n := by
  letI := secGroup G hcomm
  cases n with
  | ofNat k =>
      show G.nsmul _ k x = x ^ (k : ℤ)
      rw [zpow_natCast]
      exact nsmul_eq_pow G hcomm k x
  | negSucc k =>
      show G.inv _ (G.nsmul _ (k + 1) x) = x ^ Int.negSucc k
      rw [zpow_negSucc, nsmul_eq_pow G hcomm]
      rfl

theorem linComb_eq (P Q : Section W) (a b : ℕ) :
    letI := secGroup G hcomm; linComb G P Q a b = P ^ a * Q ^ b := by
  letI := secGroup G hcomm
  show G.mul _ (G.nsmul _ a P) (G.nsmul _ b Q) = _
  rw [nsmul_eq_pow G hcomm, nsmul_eq_pow G hcomm]
  rfl

theorem zlinComb_eq (P Q : Section W) (a b : ℤ) :
    letI := secGroup G hcomm; ModularCurve.LevelRelabelling.zlinComb G P Q a b = P ^ a * Q ^ b := by
  letI := secGroup G hcomm
  show G.mul _ (ModularCurve.LevelRelabelling.zsmulSection G a P)
    (ModularCurve.LevelRelabelling.zsmulSection G b Q) = _
  rw [zsmulSection_eq_zpow G hcomm, zsmulSection_eq_zpow G hcomm]
  rfl

omit hcomm in

theorem val_nsmul_id (n : ℕ) (P : Section W) : (G.nsmul (𝟙 _) n P).1 = P.1 ≫ G.schemeNsmul n := by
  have hnat := G.nsmul_natural (projModelStrCR W) (𝟙 _) P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := projModelStrCR W)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hid] at hnat
  rw [← hnat]
  rfl

omit hcomm in
theorem prodKerGraph_congr {𝒞 S T' : Scheme.{u}} (f : 𝒞 ⟶ S) {t : T' ⟶ S} {r : ℕ}
    {a b : Fin r → (T' ⟶ 𝒞)} (ha : ∀ i, a i ≫ f = t) (hb : ∀ i, b i ≫ f = t) (h : a = b) :
    prodKerGraph f a ha = prodKerGraph f b hb := by
  subst h
  rfl

omit hcomm in

theorem nsmul_eq_one_of_isDrinfeldBasis {q : ℕ} (P Q : Section W) (h : IsDrinfeldBasis G q P Q)
    (i : Fin (q * q)) (X : Section W) (hX : linComb G P Q (i.val / q) (i.val % q) = X) :
    G.nsmul (𝟙 _) q X = G.one _ := by

  haveI : IsSeparated (projModelStrCR W) := by
    unfold projModelStrCR
    infer_instance
  haveI hone : IsClosedImmersion (G.one (𝟙 (base (T := T)))).1 := by
    have : IsClosedImmersion ((G.one (𝟙 (base (T := T)))).1 ≫ projModelStrCR W) := by
      rw [(G.one _).2]
      infer_instance
    exact IsClosedImmersion.of_comp _ (projModelStrCR W)

  have hfac : toPullbackId (W := W) ≫ pullback.fst (projModelStrCR W) (𝟙 _) = 𝟙 _ :=
    pullback.lift_fst _ _ _
  haveI : IsIso (toPullbackId (W := W)) := by
    haveI : IsIso (toPullbackId (W := W) ≫ pullback.fst (projModelStrCR W) (𝟙 _)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.fst (projModelStrCR W) (𝟙 _))

  set ι := pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ toPullbackId (W := W)
    with hι
  haveI : IsClosedImmersion ι := inferInstance
  have hker : torsionIdeal G q = ι.ker := rfl

  set γ := graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i) with hγ
  have hle : ι.ker ≤ γ.ker := by
    rw [← hker, ← h]
    show prodKerGraph _ _ _ ≤ _
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [ideal_prodKerGraph]
    exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))

  set l := IsClosedImmersion.lift ι γ hle with hl
  have hlι : l ≫ ι = γ := IsClosedImmersion.lift_fac _ _ _
  have hX1 : basisTuple G q P Q i = X.1 := congrArg Subtype.val hX
  have h1 : l ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 = X.1 := by
    have h' := congrArg (· ≫ pullback.fst (projModelStrCR W) (𝟙 _)) hlι
    simp only [Category.assoc, hι, hfac, Category.comp_id, hγ, graphOver_fst] at h'
    rw [h', hX1]
  have h2 : l ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 = 𝟙 _ := by
    have e1 : (l ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1) ≫
        ((G.one (𝟙 (base (T := T)))).1 ≫ projModelStrCR W) =
        (l ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1) ≫
          G.schemeNsmul q ≫ projModelStrCR W := by
      simp only [Category.assoc]
      rw [← pullback.condition_assoc]
    rw [(G.one _).2, Category.comp_id, G.schemeNsmul_over, h1, X.2] at e1
    exact e1

  apply Subtype.ext
  rw [val_nsmul_id, ← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, Category.id_comp]

theorem basisTuple_relabel {q : ℕ} [NeZero q] (P Q : Section W)
    (hP : G.nsmul (𝟙 _) q P = G.one _) (hQ : G.nsmul (𝟙 _) q Q = G.one _)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) (i : Fin (q * q)) :
    basisTuple G q
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) i =
    basisTuple G q P Q (perm q g hg i) := by
  letI := secGroup G hcomm
  have hP' : P ^ q = 1 := by rw [← nsmul_eq_pow G hcomm]; exact hP
  have hQ' : Q ^ q = 1 := by rw [← nsmul_eq_pow G hcomm]; exact hQ

  have hcoord := coord_perm q g hg i
  simp only [coord, linMap, Prod.mk.injEq] at hcoord
  obtain ⟨hc1, hc2⟩ := hcoord

  show (linComb G _ _ (i.val / q) (i.val % q)).1 =
    (linComb G P Q ((perm q g hg i).val / q) ((perm q g hg i).val % q)).1
  congr 1
  rw [linComb_eq G hcomm, linComb_eq G hcomm, zlinComb_eq G hcomm, zlinComb_eq G hcomm, combo_eq,
    ← zpow_natCast P ((perm q g hg i).val / q), ← zpow_natCast Q ((perm q g hg i).val % q)]
  congr 1
  · apply zpow_eq_zpow_of_cast_eq hP'
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [hc1]
    ring
  · apply zpow_eq_zpow_of_cast_eq hQ'
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [hc2]
    ring

theorem main (q : ℕ) (P Q : Section W) (h : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    IsDrinfeldBasis G q
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) := by
  set P' := ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0) with hP'
  set Q' := ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1) with hQ'
  unfold IsDrinfeldBasis at h ⊢
  rw [← h]
  unfold basisDivisor
  rcases Nat.lt_or_ge q 2 with hq | hq
  ·
    apply prodKerGraph_congr
    funext i
    interval_cases q
    · exact absurd i.isLt (by omega)
    · have hi : i.val = 0 := by omega
      have hc : ∀ X Y : Section W, basisTuple G 1 X Y i = (G.mul (𝟙 _) (G.one _) (G.one _)).1 := by
        intro X Y
        simp only [basisTuple, linComb, hi, Nat.zero_div, Nat.zero_mod]
        rfl
      rw [hc, hc]
  ·
    haveI : NeZero q := ⟨by omega⟩
    have hqq : q < q * q := by nlinarith
    have h1q : 1 < q * q := lt_trans (by omega) hqq

    have hP : G.nsmul (𝟙 _) q P = G.one _ := by
      refine nsmul_eq_one_of_isDrinfeldBasis G P Q h ⟨q, hqq⟩ P ?_
      show linComb G P Q (q / q) (q % q) = P
      rw [Nat.div_self (by omega), Nat.mod_self]
      show G.mul _ (G.nsmul _ 1 P) (G.nsmul _ 0 Q) = P
      rw [G.nsmul_one_apply, G.nsmul_zero, G.mul_one]
    have hQ : G.nsmul (𝟙 _) q Q = G.one _ := by
      refine nsmul_eq_one_of_isDrinfeldBasis G P Q h ⟨1, h1q⟩ Q ?_
      show linComb G P Q (1 / q) (1 % q) = Q
      rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      show G.mul _ (G.nsmul _ 0 P) (G.nsmul _ 1 Q) = Q
      rw [G.nsmul_one_apply, G.nsmul_zero, G.one_mul]

    have key : basisTuple G q P' Q' = fun i => basisTuple G q P Q (perm q g hg i) := by
      funext i
      exact basisTuple_relabel G hcomm P Q hP hQ g hg i
    rw [prodKerGraph_congr (projModelStrCR W) (basisTuple_over G q P' Q')
      (fun i => basisTuple_over G q P Q (perm q g hg i)) key]
    exact prodKerGraph_comp_equiv (projModelStrCR W) (perm q g hg) (basisTuple G q P Q)
      (basisTuple_over G q P Q)

end Sections

end P2mKcDrinfeldRelabel
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det.P2mKcDrinfeldRelabel"

theorem solution
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)
    (q : ℕ) (P Q : Section W) (h : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    IsDrinfeldBasis G q
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) :=
  P2mKcDrinfeldRelabel.main G hcomm q P Q h g hg

end S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det (solution)
