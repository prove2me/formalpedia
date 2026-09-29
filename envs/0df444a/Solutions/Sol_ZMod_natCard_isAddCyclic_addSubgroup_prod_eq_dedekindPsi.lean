-- Prove2me | solution 1 for ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/6a58e9d0-58e3-5950-b265-82c9acbf46b4

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ProjectiveLine
import Theorems.Thm_ModularCurve_card_projectiveLine_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "dedekindPsi IsUnimodularRow UnimodularRow ProjectiveLine card_projectiveLine_zmod"
p2m_open "ModularCurve"

open AddSubgroup

section OrderUnimodular

variable (N : ℕ)

private theorem nsmul_pair (n : ℕ) (x : ZMod N × ZMod N) :
    n • x = (n • x.1, n • x.2) :=
  Prod.ext (map_nsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) n x)
    (map_nsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) n x)

private theorem zsmul_pair_fst (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).1 = k • x.1 :=
  map_zsmul (AddMonoidHom.fst (ZMod N) (ZMod N)) k x

private theorem zsmul_pair_snd (k : ℤ) (x : ZMod N × ZMod N) :
    (k • x).2 = k • x.2 :=
  map_zsmul (AddMonoidHom.snd (ZMod N) (ZMod N)) k x

private theorem nsmul_eq_zero_of_dvd_mul_val {m : ℕ} {z : ZMod N} [NeZero N]
    (h : N ∣ m * z.val) : m • z = 0 :=
  calc m • z = (m : ZMod N) * z := nsmul_eq_mul m z
    _ = (m : ZMod N) * (z.val : ZMod N) := by rw [ZMod.natCast_zmod_val]
    _ = ((m * z.val : ℕ) : ZMod N) := (Nat.cast_mul _ _).symm
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h

variable [NeZero N]

namespace IsUnimodularRow p2m_export "ModularCurve.IsUnimodularRow" "map" end IsUnimodularRow
p2m_open_scoped "ModularCurve.IsUnimodularRow" in
omit [NeZero N] in

theorem IsUnimodularRow.addOrderOf_eq {a c : ZMod N} (h : IsUnimodularRow a c) :
    addOrderOf ((a, c) : ZMod N × ZMod N) = N := by
  obtain ⟨x, y, hxy⟩ := h

  have hdvdN : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N := by
    refine addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
    rw [nsmul_pair]
    have hza : N • a = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have hzc : N • c = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hza, hzc]
    rfl

  have hN : N ∣ addOrderOf ((a, c) : ZMod N × ZMod N) := by
    have hsmul : addOrderOf ((a, c) : ZMod N × ZMod N) • ((a, c) : ZMod N × ZMod N) = 0 :=
      addOrderOf_nsmul_eq_zero _
    rw [nsmul_pair] at hsmul
    have ha : addOrderOf ((a, c) : ZMod N × ZMod N) • a = 0 := congrArg Prod.fst hsmul
    have hc : addOrderOf ((a, c) : ZMod N × ZMod N) • c = 0 := congrArg Prod.snd hsmul
    rw [nsmul_eq_mul] at ha hc
    have hzero : ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N) = 0 := by
      calc ((addOrderOf ((a, c) : ZMod N × ZMod N) : ℕ) : ZMod N)
          = (addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * (x * a + y * c) := by
            rw [hxy, mul_one]
        _ = x * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * a)
              + y * ((addOrderOf ((a, c) : ZMod N × ZMod N) : ZMod N) * c) := by ring
        _ = 0 := by rw [ha, hc, mul_zero, mul_zero, add_zero]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  exact Nat.dvd_antisymm hdvdN hN

theorem isUnimodularRow_of_addOrderOf_eq {a c : ZMod N}
    (h : addOrderOf ((a, c) : ZMod N × ZMod N) = N) : IsUnimodularRow a c := by
  have hN0 : N ≠ 0 := NeZero.ne N
  set d : ℕ := Nat.gcd (Nat.gcd a.val c.val) N with hd
  have hdN : d ∣ N := Nat.gcd_dvd_right _ _
  have hdA : d ∣ a.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
  have hdC : d ∣ c.val := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)

  have hd1 : d = 1 := by
    have hkill : (N / d) • ((a, c) : ZMod N × ZMod N) = 0 := by
      rw [nsmul_pair]
      have hka : (N / d) • a = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨A', hA'⟩ := hdA
        exact ⟨A', by rw [hA', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      have hkc : (N / d) • c = 0 := by
        refine nsmul_eq_zero_of_dvd_mul_val N ?_
        obtain ⟨C', hC'⟩ := hdC
        exact ⟨C', by rw [hC', ← mul_assoc, Nat.div_mul_cancel hdN]⟩
      rw [hka, hkc]
      rfl
    have horder : addOrderOf ((a, c) : ZMod N × ZMod N) ∣ N / d :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
    rw [h] at horder
    have hdivdvd : N / d ∣ N := Nat.div_dvd_of_dvd hdN
    have hNd : N / d = N := Nat.dvd_antisymm hdivdvd horder
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdN
    rw [hNd] at hmul
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) (hmul.trans (one_mul N).symm)

  have hcop : Nat.Coprime (Nat.gcd a.val c.val) N := hd1
  have hunit : IsUnit ((Nat.gcd a.val c.val : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime _ N).mpr hcop
  obtain ⟨u, hu⟩ := hunit
  have hbez := Nat.gcd_eq_gcd_ab a.val c.val
  have hcast : ((Nat.gcd a.val c.val : ℕ) : ZMod N)
      = a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N) + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N) := by
    have hℤ := congrArg (fun z : ℤ => (Int.castRingHom (ZMod N)) z) hbez
    simp only [map_add, map_mul, Int.coe_castRingHom] at hℤ
    rw [Int.cast_natCast, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at hℤ
    exact hℤ
  refine ⟨((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N),
    ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N), ?_⟩
  calc ((Nat.gcdA a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * a
        + ((Nat.gcdB a.val c.val : ℤ) : ZMod N) * (↑u⁻¹ : ZMod N) * c
      = (a * ((Nat.gcdA a.val c.val : ℤ) : ZMod N)
          + c * ((Nat.gcdB a.val c.val : ℤ) : ZMod N)) * (↑u⁻¹ : ZMod N) := by ring
    _ = ((Nat.gcd a.val c.val : ℕ) : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [← hcast]
    _ = (↑u : ZMod N) * (↑u⁻¹ : ZMod N) := by rw [hu]
    _ = 1 := u.mul_inv

theorem isUnimodularRow_iff_addOrderOf_eq {a c : ZMod N} :
    IsUnimodularRow a c ↔ addOrderOf ((a, c) : ZMod N × ZMod N) = N :=
  ⟨IsUnimodularRow.addOrderOf_eq N, isUnimodularRow_of_addOrderOf_eq N⟩

end OrderUnimodular

section Scaling

variable (N : ℕ) [NeZero N]

theorem zmultiples_unit_mul (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) :
    AddSubgroup.zmultiples ((((u : ZMod N) * x.1, (u : ZMod N) * x.2)) : ZMod N × ZMod N)
      = AddSubgroup.zmultiples x := by
  have key : ∀ (w : (ZMod N)ˣ) (y : ZMod N × ZMod N),
      (((w : ZMod N) * y.1, (w : ZMod N) * y.2) : ZMod N × ZMod N) ∈ AddSubgroup.zmultiples y := by
    intro w y
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((w : ZMod N).val : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · show ((((w : ZMod N).val : ℤ)) • y).1 = (w : ZMod N) * y.1
      rw [zsmul_pair_fst, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    · show ((((w : ZMod N).val : ℤ)) • y).2 = (w : ZMod N) * y.2
      rw [zsmul_pair_snd, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine le_antisymm (AddSubgroup.zmultiples_le.mpr (key u x)) (AddSubgroup.zmultiples_le.mpr ?_)

  have hmem := key u⁻¹ (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N)
  have hx : ((((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).1,
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).2)
        : ZMod N × ZMod N) = x := by
    have h1 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.1) = x.1 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    have h2 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.2) = x.2 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    exact Prod.ext h1 h2
  rwa [hx] at hmem

omit [NeZero N] in

theorem eq_of_mul_unimodularRow_eq {a c : ZMod N} (h : IsUnimodularRow a c) {r s : ZMod N}
    (h1 : r * a = s * a) (h2 : r * c = s * c) : r = s := by
  obtain ⟨x, y, hxy⟩ := h
  calc r = r * (x * a + y * c) := by rw [hxy, mul_one]
    _ = x * (r * a) + y * (r * c) := by ring
    _ = x * (s * a) + y * (s * c) := by rw [h1, h2]
    _ = s * (x * a + y * c) := by ring
    _ = s := by rw [hxy, mul_one]

p2m_open_scoped "ModularCurve.IsUnimodularRow" in
omit [NeZero N] in

theorem IsUnimodularRow.unit_mul {a c : ZMod N} (h : IsUnimodularRow a c) (u : (ZMod N)ˣ) :
    IsUnimodularRow ((u : ZMod N) * a) ((u : ZMod N) * c) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), ?_⟩
  calc x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * a)
        + y * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * c)
      = (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (x * a)
          + (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N)) * (y * c) := by ring
    _ = x * a + y * c := by rw [u.inv_mul, one_mul, one_mul]
    _ = 1 := hxy

end Scaling

section Bijection

variable (N : ℕ) [NeZero N]

def unimodularRowToCyclicAddSubgroup (v : UnimodularRow (ZMod N)) :
    {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  ⟨AddSubgroup.zmultiples v.1,
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨v.1, rfl⟩,
    by rw [Nat.card_zmultiples, IsUnimodularRow.addOrderOf_eq N v.2]⟩

def projectiveLineToCyclicAddSubgroup :
    ProjectiveLine (ZMod N) → {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Quotient.lift (unimodularRowToCyclicAddSubgroup N) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Subtype.ext ?_
    show AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1
    have hw : w.1 = (((u : ZMod N) * v.1.1, (u : ZMod N) * v.1.2) : ZMod N × ZMod N) := by
      rw [h1, h2]
    rw [hw, zmultiples_unit_mul]

@[scoped simp]
theorem projectiveLineToCyclicAddSubgroup_mk (v : UnimodularRow (ZMod N)) :
    projectiveLineToCyclicAddSubgroup N ⟦v⟧ = unimodularRowToCyclicAddSubgroup N v :=
  rfl

theorem projectiveLineToCyclicAddSubgroup_injective :
    Function.Injective (projectiveLineToCyclicAddSubgroup N) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro v w hvw
  have hsub : AddSubgroup.zmultiples v.1 = AddSubgroup.zmultiples w.1 :=
    congrArg Subtype.val hvw

  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub ▸ AddSubgroup.mem_zmultiples w.1)

  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (hsub.symm ▸ AddSubgroup.mem_zmultiples v.1)
  have hk1 : ((k : ZMod N)) * v.1.1 = w.1.1 := by
    have h := congrArg Prod.fst hk; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hk2 : ((k : ZMod N)) * v.1.2 = w.1.2 := by
    have h := congrArg Prod.snd hk; rwa [zsmul_pair_snd, zsmul_eq_mul] at h
  have hm1 : ((m : ZMod N)) * w.1.1 = v.1.1 := by
    have h := congrArg Prod.fst hm; rwa [zsmul_pair_fst, zsmul_eq_mul] at h
  have hm2 : ((m : ZMod N)) * w.1.2 = v.1.2 := by
    have h := congrArg Prod.snd hm; rwa [zsmul_pair_snd, zsmul_eq_mul] at h

  have hmk : ((m : ZMod N)) * ((k : ZMod N)) = 1 := by
    refine eq_of_mul_unimodularRow_eq N v.2 ?_ ?_
    · rw [mul_assoc, hk1, hm1, one_mul]
    · rw [mul_assoc, hk2, hm2, one_mul]
  refine Quotient.sound ⟨⟨(k : ZMod N), (m : ZMod N), by rw [mul_comm]; exact hmk, hmk⟩, ?_, ?_⟩
  · exact hk1
  · exact hk2

theorem projectiveLineToCyclicAddSubgroup_surjective :
    Function.Surjective (projectiveLineToCyclicAddSubgroup N) := by
  rintro ⟨H, hcyc, hcard⟩
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
  have horder : addOrderOf g = N := by
    have := Nat.card_zmultiples g
    rw [hg, hcard] at this
    exact this.symm
  have hrow : IsUnimodularRow g.1 g.2 := by
    refine isUnimodularRow_of_addOrderOf_eq N ?_
    have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
    rw [hg', horder]
  refine ⟨⟦⟨(g.1, g.2), hrow⟩⟧, ?_⟩
  refine Subtype.ext ?_
  show AddSubgroup.zmultiples ((g.1, g.2) : ZMod N × ZMod N) = H
  have hg' : ((g.1, g.2) : ZMod N × ZMod N) = g := rfl
  rw [hg', hg]

def projectiveLineEquivCyclicAddSubgroup :
    ProjectiveLine (ZMod N) ≃ {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N} :=
  Equiv.ofBijective (projectiveLineToCyclicAddSubgroup N)
    ⟨projectiveLineToCyclicAddSubgroup_injective N, projectiveLineToCyclicAddSubgroup_surjective N⟩

end Bijection

section Headline

variable (N : ℕ) [NeZero N]

theorem card_cyclicAddSubgroup_eq_card_projectiveLine :
    Nat.card {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N}
      = Nat.card (ProjectiveLine (ZMod N)) :=
  (Nat.card_congr (projectiveLineEquivCyclicAddSubgroup N)).symm

theorem card_cyclicAddSubgroup_eq_dedekindPsi :
    Nat.card {H : AddSubgroup (ZMod N × ZMod N) // IsAddCyclic H ∧ Nat.card H = N}
      = dedekindPsi N := by
  rw [card_cyclicAddSubgroup_eq_card_projectiveLine,
    card_projectiveLine_zmod N (NeZero.ne N)]

end Headline

end ModularCurve
p2m_reactivate "P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.ModularCurve"

end
p2m_reactivate "P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.ModularCurve"

theorem solution (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n :=
  ModularCurve.card_cyclicAddSubgroup_eq_dedekindPsi n

end S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
end P2MW
export P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi (solution)
