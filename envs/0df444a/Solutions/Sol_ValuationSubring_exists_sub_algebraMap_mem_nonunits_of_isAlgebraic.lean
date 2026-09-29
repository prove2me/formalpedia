-- Prove2me | solution 1 for ValuationSubring.exists_sub_algebraMap_mem_nonunits_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/80986ef9-5532-52fd-ae60-b76679957139

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic

set_option autoImplicit false

noncomputable section

namespace ValuationSubring
p2m_export "ValuationSubring" "subtype coe_mem_nonunits_iff mem_nonunits_iff_exists_mem_maximalIdeal toSubring algebraMap_apply ext zero_mem nonunits mem_nonunits_iff nonunits_subset valuation_le_one_iff algebra valuation"
p2m_open "ValuationSubring"
namespace ResidueAlgebraic

open IsLocalRing Polynomial

section Over

variable {L : Type*} [Field L] {L' : Type*} [Field L']

def overHom (f : L →+* L') (A : ValuationSubring L) (O : ValuationSubring L')
    (h : ∀ a, f a ∈ O ↔ a ∈ A) : A →+* O where
  toFun a := ⟨f a, (h a).2 a.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f (a : L) (b : L))
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : L) (b : L))

variable (f : L →+* L') (A : ValuationSubring L) (O : ValuationSubring L')
  (h : ∀ a, f a ∈ O ↔ a ∈ A)

scoped instance isLocalHom_overHom : IsLocalHom (overHom f A O h) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 ha
  have hy' : f a * (y : L') = 1 := by
    have := congrArg (fun z : O => (z : L')) hy
    simp at this
    exact this
  have ha0 : (a : L) ≠ 0 := fun h0 => by
    rw [h0, map_zero, zero_mul] at hy'
    exact zero_ne_one hy'
  have hinvO : (f a)⁻¹ ∈ O := by
    rw [← (eq_inv_of_mul_eq_one_right hy')]; exact y.2
  have hinvA : (a : L)⁻¹ ∈ A := by rw [← h, map_inv₀]; exact hinvO
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem residue_overHom_eq_zero_of_mem_nonunits {a : L} (ha : a ∈ A.nonunits) :
    residue O ⟨f a, (h a).2 (A.nonunits_subset ha)⟩ = 0 := by
  have hmax : (⟨a, A.nonunits_subset ha⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp ha
  have : overHom f A O h ⟨a, A.nonunits_subset ha⟩ ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff] at hmax ⊢
    exact fun hu => hmax ((isUnit_map_iff (overHom f A O h) _).1 hu)
  exact (IsLocalRing.residue_eq_zero_iff _).2 this

end Over

section Main

variable {K : Type*} [Field K] [IsAlgClosed K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  {Ω' : Type*} [Field Ω'] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']

theorem exists_sub_algebraMap_mem_nonunits [Algebra.IsAlgebraic Ω Ω']
    (A : ValuationSubring Ω) (hK : ∀ c : K, algebraMap K Ω c ∈ A)
    (hres : ∀ a : Ω, a ∈ A → ∃ c : K, a - algebraMap K Ω c ∈ A.nonunits)
    (O : ValuationSubring Ω') (hO : ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ A)
    (z : Ω') (hz : z ∈ O) : ∃ c : K, z - algebraMap K Ω' c ∈ O.nonunits := by
  classical
  have hKO : ∀ c : K, algebraMap K Ω' c ∈ O := fun c => by
    rw [IsScalarTower.algebraMap_apply K Ω Ω', hO]; exact hK c

  letI algKO : Algebra K O := ((algebraMap K Ω').codRestrict O.toSubring hKO).toAlgebra
  have halgKO : ∀ c : K, ((algebraMap K O c : O) : Ω') = algebraMap K Ω' c := fun _ => rfl

  obtain ⟨p, hp0, hpz⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := Ω) z)
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image p.support (fun i => A.valuation (p.coeff i)) hsupp
  set c₀ : Ω := p.coeff i₀ with hc₀def
  have hc₀ : c₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  set q : Polynomial Ω := Polynomial.C c₀⁻¹ * p with hqdef
  have hqcoeff : ∀ i, q.coeff i = c₀⁻¹ * p.coeff i := fun i => by
    rw [hqdef, Polynomial.coeff_C_mul]
  have hqmem : ∀ i, q.coeff i ∈ A := by
    intro i
    rw [hqcoeff]
    by_cases hi : i ∈ p.support
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      have hle := hmax i hi
      have hv0 : A.valuation c₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hc₀
      calc (A.valuation c₀)⁻¹ * A.valuation (p.coeff i)
          ≤ (A.valuation c₀)⁻¹ * A.valuation c₀ := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hv0
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact A.zero_mem
  have hqi₀ : q.coeff i₀ = 1 := by rw [hqcoeff, ← hc₀def, inv_mul_cancel₀ hc₀]
  have hqz : Polynomial.aeval z q = 0 := by
    rw [hqdef, map_mul, hpz, mul_zero]

  choose c hc using fun i => hres (q.coeff i) (hqmem i)
  have hone : (1 : Ω) ∉ A.nonunits := by simp [ValuationSubring.mem_nonunits_iff]
  have hci₀ : c i₀ ≠ 0 := by
    intro h0
    have := hc i₀
    rw [hqi₀, h0, map_zero, sub_zero] at this
    exact hone this

  have hcoef_res : ∀ i, residue O ⟨algebraMap Ω Ω' (q.coeff i), (hO _).2 (hqmem i)⟩ =
      algebraMap K (ResidueField O) (c i) := by
    intro i
    rw [IsScalarTower.algebraMap_apply K O (ResidueField O), ResidueField.algebraMap_eq,
      ← sub_eq_zero, ← map_sub]
    have hmem : q.coeff i - algebraMap K Ω (c i) ∈ A.nonunits := hc i
    have h0 := residue_overHom_eq_zero_of_mem_nonunits (algebraMap Ω Ω') A O hO hmem
    convert h0 using 2
    apply Subtype.ext
    change algebraMap Ω Ω' (q.coeff i) - algebraMap K Ω' (c i) = algebraMap Ω Ω' (q.coeff i - _)
    rw [map_sub, ← IsScalarTower.algebraMap_apply]

  set zO : O := ⟨z, hz⟩ with hzOdef
  set PO : Polynomial O := ∑ i ∈ q.support,
      Polynomial.C (⟨algebraMap Ω Ω' (q.coeff i), (hO _).2 (hqmem i)⟩ : O) * Polynomial.X ^ i
    with hPOdef
  set r : Polynomial K := ∑ i ∈ q.support, Polynomial.C (c i) * Polynomial.X ^ i with hrdef
  have hPOcoeff : ∀ n, PO.coeff n =
      if n ∈ q.support then (⟨algebraMap Ω Ω' (q.coeff n), (hO _).2 (hqmem n)⟩ : O) else 0 := by
    intro n
    rw [hPOdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  have hrcoeff : ∀ n, r.coeff n = if n ∈ q.support then c n else 0 := by
    intro n
    rw [hrdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
  have hi₀q : i₀ ∈ q.support := Polynomial.mem_support_iff.mpr (by rw [hqi₀]; exact one_ne_zero)
  have hr0 : r ≠ 0 := by
    intro h0
    have := congrArg (fun s : Polynomial K => s.coeff i₀) h0
    simp only [hrcoeff, hi₀q, if_true, Polynomial.coeff_zero] at this
    exact hci₀ this

  have hPOmap : PO.map O.subtype = q.map (algebraMap Ω Ω') := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hPOcoeff]
    by_cases hn : n ∈ q.support
    · rw [if_pos hn]; rfl
    · rw [if_neg hn, map_zero, Polynomial.notMem_support_iff.mp hn, map_zero]

  have hPOeval : PO.eval zO = 0 := by
    apply Subtype.ext
    change O.subtype (PO.eval zO) = 0
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hPOmap, Polynomial.eval_map_algebraMap]
    exact hqz

  have hPOres : PO.map (residue O) = r.map (algebraMap K (ResidueField O)) := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hPOcoeff, hrcoeff]
    by_cases hn : n ∈ q.support
    · rw [if_pos hn, if_pos hn, hcoef_res]
    · rw [if_neg hn, if_neg hn, map_zero, map_zero]

  have halg : IsAlgebraic K (residue O zO) := by
    refine ⟨r, hr0, ?_⟩
    rw [← Polynomial.eval_map_algebraMap, ← hPOres, Polynomial.eval_map, Polynomial.eval₂_hom,
      hPOeval, map_zero]
  obtain ⟨c', hc'⟩ : ∃ c' : K, algebraMap K (ResidueField O) c' = residue O zO := by
    have hint : IsIntegral K (residue O zO) := halg.isIntegral
    have hdeg : (minpoly K (residue O zO)).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨c', hc'⟩ := minpoly.degree_eq_one_iff.1 hdeg
    exact ⟨c', hc'⟩
  refine ⟨c', ?_⟩
  have hmem : z - algebraMap K Ω' c' ∈ O := sub_mem hz (hKO c')
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hmem, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have heq : (⟨z - algebraMap K Ω' c', hmem⟩ : O) = zO - algebraMap K O c' := Subtype.ext rfl
  rw [heq, map_sub, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply, hc',
    ResidueField.algebraMap_eq, sub_self]

end Main

end ResidueAlgebraic
p2m_reactivate "P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.ValuationSubring.ResidueAlgebraic"
end ValuationSubring
p2m_reactivate "P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.ValuationSubring.ResidueAlgebraic P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.ValuationSubring"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.ValuationSubring.ResidueAlgebraic P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic.ValuationSubring"

universe u v w in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {Ω : Type v} [Field Ω] [Algebra K Ω]
    {Ω' : Type w} [Field Ω'] [Algebra Ω Ω'] [Algebra K Ω'] [IsScalarTower K Ω Ω']
    [Algebra.IsAlgebraic Ω Ω']
    (A : ValuationSubring Ω) (hK : ∀ c : K, algebraMap K Ω c ∈ A)
    (hres : ∀ a : Ω, a ∈ A → ∃ c : K, a - algebraMap K Ω c ∈ A.nonunits)
    (O : ValuationSubring Ω') (hO : ∀ a : Ω, algebraMap Ω Ω' a ∈ O ↔ a ∈ A)
    (z : Ω') (hz : z ∈ O) : ∃ c : K, z - algebraMap K Ω' c ∈ O.nonunits :=
  ValuationSubring.ResidueAlgebraic.exists_sub_algebraMap_mem_nonunits A hK hres O hO z hz

end S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic
end P2MW
export P2MW.S_ValuationSubring_exists_sub_algebraMap_mem_nonunits_of_isAlgebraic (solution)
