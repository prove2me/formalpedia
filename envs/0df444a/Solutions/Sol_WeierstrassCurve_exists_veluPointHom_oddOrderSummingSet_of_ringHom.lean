-- Prove2me | solution 1 for WeierstrassCurve.exists_veluPointHom_oddOrderSummingSet_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a044e990-8267-5d17-b2cb-c4942d1050ce

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom.WeierstrassCurve"

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map map_b₂ b₂ a₄ a₆ Affine.Point.map_injective toAffine Affine.Point map_injective map_a₆ Affine.Point.map map_a₁ map_a₄ Affine.map_nonsingular map_a₂ map_a₃ veluGx veluGy veluT veluU veluW veluTSum veluWSum veluQuotient veluX veluY Affine.Point.coordsOrZero_zero oddOrderSummingSet"
namespace VeluDescentAux
p2m_open "WeierstrassCurve"

section MapLemmas

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] (f : F →+* K) (W : WeierstrassCurve F)

abbrev pm : F × F → K × K := Prod.map f f

theorem pm_injective : Function.Injective (pm f) :=
  fun a b h => Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))

theorem map_veluGx (x y : F) : (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₁,
    map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem map_veluGy (x y : F) : (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_neg, map_add, map_mul,
    map_ofNat]

theorem map_veluT (x y : F) : (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [veluT, map_veluGx, map_veluGy, WeierstrassCurve.map_a₁, map_sub, map_mul, map_ofNat]

theorem map_veluU (x y : F) : (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp only [veluU, map_veluGy, map_pow]

theorem map_veluW (x y : F) : (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp only [veluW, map_veluU, map_veluT, map_add, map_mul]

theorem map_veluTSum (S : Finset (F × F)) :
    (W.map f).veluTSum (S.image (pm f)) = f (W.veluTSum S) := by
  rw [veluTSum, veluTSum, Finset.sum_image (fun a _ b _ h => pm_injective f h), map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT f W P.1 P.2

theorem map_veluWSum (S : Finset (F × F)) :
    (W.map f).veluWSum (S.image (pm f)) = f (W.veluWSum S) := by
  rw [veluWSum, veluWSum, Finset.sum_image (fun a _ b _ h => pm_injective f h), map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW f W P.1 P.2

theorem map_veluQuotient (S : Finset (F × F)) :
    (W.map f).veluQuotient (S.image (pm f)) = (W.veluQuotient S).map f := by
  ext
  · rfl
  · rfl
  · rfl
  · show (W.map f).a₄ - 5 * (W.map f).veluTSum (S.image (pm f)) = f (W.a₄ - 5 * W.veluTSum S)
    rw [map_veluTSum, WeierstrassCurve.map_a₄, map_sub, map_mul, map_ofNat]
  · show (W.map f).a₆ - (W.map f).b₂ * (W.map f).veluTSum (S.image (pm f))
        - 7 * (W.map f).veluWSum (S.image (pm f))
      = f (W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S)
    rw [map_veluTSum, map_veluWSum, WeierstrassCurve.map_a₆, WeierstrassCurve.map_b₂, map_sub, map_sub,
      map_mul, map_mul, map_ofNat]

theorem map_veluX (S : Finset (F × F)) (x : F) :
    (W.map f).veluX (S.image (pm f)) (f x) = f (W.veluX S x) := by
  rw [veluX, veluX, Finset.sum_image (fun a _ b _ h => pm_injective f h), map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun P _ => ?_)
  simp only [pm, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_add, map_div₀, map_sub,
    map_pow]

theorem map_veluY (S : Finset (F × F)) (x y : F) :
    (W.map f).veluY (S.image (pm f)) (f x) (f y) = f (W.veluY S x y) := by
  rw [veluY, veluY, Finset.sum_image (fun a _ b _ h => pm_injective f h), map_sub, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun P _ => ?_)
  simp only [pm, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_veluGx, map_veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_div₀, map_sub, map_pow, map_mul,
    map_ofNat]

end MapLemmas

section Points

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq K]
  (W : WeierstrassCurve F)

def ι : W.toAffine.Point →+ (W.map (algebraMap F K)).toAffine.Point :=
  (WeierstrassCurve.Affine.Point.map (Algebra.ofId F K) :
    (W⁄F).toAffine.Point →+ (W⁄K).toAffine.Point)

theorem ι_some (x y : F) (h : W.toAffine.Nonsingular x y) :
    ι (K := K) W (.some x y h) = .some (algebraMap F K x) (algebraMap F K y)
      ((WeierstrassCurve.Affine.map_nonsingular _ (algebraMap F K).injective x y).mpr h) := by
  rfl

theorem ι_injective : Function.Injective (ι (K := K) W) :=
  WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId F K)

theorem coordsOrZero_ι (P : W.toAffine.Point) :
    (ι (K := K) W P).coordsOrZero = Prod.map (algebraMap F K) (algebraMap F K) P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((.zero : (W.map (algebraMap F K)).toAffine.Point)).coordsOrZero
      = Prod.map (algebraMap F K) (algebraMap F K) ((.zero : W.toAffine.Point)).coordsOrZero
    rw [WeierstrassCurve.Affine.Point.coordsOrZero_zero, WeierstrassCurve.Affine.Point.coordsOrZero_zero]
    simp
  · rw [ι_some]
    rfl

theorem oddOrderSummingSet_ι (Q : W.toAffine.Point) (n : ℕ) :
    (W.map (algebraMap F K)).oddOrderSummingSet (ι W Q) n
      = (W.oddOrderSummingSet Q n).image (pm (algebraMap F K)) := by
  rw [oddOrderSummingSet, oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show (k • ι W Q).coordsOrZero = pm (algebraMap F K) ((k • Q).coordsOrZero)
  rw [← map_nsmul, coordsOrZero_ι]

theorem mem_zmultiples_ι_iff {P Q : W.toAffine.Point} :
    ι (K := K) W P ∈ AddSubgroup.zmultiples (ι (K := K) W Q) ↔ P ∈ AddSubgroup.zmultiples Q := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ι_injective (K := K) W ?_⟩
    rw [map_zsmul]
    exact hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, (map_zsmul _ _ _).symm⟩

end Points

section Congr

variable {K : Type*} [Field K] [DecidableEq K]

def pointCongr {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) : V₁.toAffine.Point ≃+ V₂.toAffine.Point := by
  subst h; exact AddEquiv.refl _

theorem pointCongr_some {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) (x y : K)
    (h₁ : V₁.toAffine.Nonsingular x y) :
    pointCongr h (.some x y h₁) = .some x y (h ▸ h₁) := by
  subst h; rfl

end Congr

end WeierstrassCurve.VeluDescentAux

end

open WeierstrassCurve.VeluDescentAux in

theorem solution
    {F L : Type*} [Field F] [DecidableEq F] [Field L] [DecidableEq L] (f : F →+* L)
    (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (Q : W.toAffine.Point) (hQord : addOrderOf Q = p)
    (hL : ∀ (W' : WeierstrassCurve L) [W'.IsElliptic] (Q' : W'.toAffine.Point), addOrderOf Q' = p →
      let S' := W'.oddOrderSummingSet Q' (p / 2)
      ∃ φ' : W'.toAffine.Point →+ (W'.veluQuotient S').toAffine.Point,
        φ'.ker = AddSubgroup.zmultiples Q' ∧
        (∀ (x y : L) (h : W'.toAffine.Nonsingular x y),
          (.some x y h : W'.toAffine.Point) ∉ AddSubgroup.zmultiples Q' →
            ∃ h', φ' (.some x y h) = .some (W'.veluX S' x) (W'.veluY S' x y) h')) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by
  classical
  intro S
  letI : Algebra F L := f.toAlgebra
  have hfa : algebraMap F L = f := RingHom.algebraMap_toAlgebra f
  set Wb : WeierstrassCurve L := W.map (algebraMap F L) with hWb
  haveI : Wb.IsElliptic := by rw [hWb]; infer_instance
  set Qb : Wb.toAffine.Point := ι (K := L) W Q with hQb
  have hQb_ord : addOrderOf Qb = p := by
    rw [hQb, ← hQord]
    exact addOrderOf_injective (ι (K := L) W) (ι_injective W) Q

  obtain ⟨φb, hkerb, hcoordb⟩ := hL Wb Qb hQb_ord
  have hSbS : Wb.oddOrderSummingSet Qb (p / 2) = S.image (pm (algebraMap F L)) :=
    oddOrderSummingSet_ι W Q (p / 2)
  have hVQ : Wb.veluQuotient (Wb.oddOrderSummingSet Qb (p / 2)) = (W.veluQuotient S).map (algebraMap F L) := by
    rw [hSbS]; exact map_veluQuotient (algebraMap F L) W S

  set ψ : Wb.toAffine.Point →+ ((W.veluQuotient S).map (algebraMap F L)).toAffine.Point :=
    (pointCongr hVQ).toAddMonoidHom.comp φb with hψ

  have hns : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
      (W.veluQuotient S).toAffine.Nonsingular (W.veluX S x) (W.veluY S x y) := by
    intro x y h hm
    have hmb : (ι (K := L) W (.some x y h) : Wb.toAffine.Point) ∉ AddSubgroup.zmultiples Qb :=
      fun hh => hm ((mem_zmultiples_ι_iff W).mp hh)
    rw [ι_some] at hmb
    obtain ⟨h', -⟩ := hcoordb (algebraMap F L x) (algebraMap F L y) _ hmb
    rw [hSbS, map_veluX, map_veluY, map_veluQuotient] at h'
    exact (WeierstrassCurve.Affine.map_nonsingular _ (algebraMap F L).injective _ _).mp h'

  let g : W.toAffine.Point → (W.veluQuotient S).toAffine.Point := fun P =>
    match P with
    | .zero => 0
    | .some x y h =>
        if hm : (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q then 0
        else .some (W.veluX S x) (W.veluY S x y) (hns x y h hm)
  have hg_zero : g 0 = 0 := rfl
  have hg_mem : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q → g (.some x y h) = 0 := by
    intro x y h hm
    simp only [g, dif_pos hm]
  have hg_nmem : ∀ (x y : F) (h : W.toAffine.Nonsingular x y)
      (hm : (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q),
      g (.some x y h) = .some (W.veluX S x) (W.veluY S x y) (hns x y h hm) := by
    intro x y h hm
    simp only [g, dif_neg hm]

  have hkey : ∀ P, ι (K := L) (W.veluQuotient S) (g P) = ψ (ι (K := L) W P) := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · show ι (K := L) (W.veluQuotient S) (g 0) = ψ (ι (K := L) W 0)
      rw [hg_zero, _root_.map_zero, _root_.map_zero, _root_.map_zero]
    · by_cases hm : (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
      · rw [hg_mem x y h hm, _root_.map_zero]
        have hk : ι (K := L) W (.some x y h) ∈ φb.ker := by
          rw [hkerb]; exact (mem_zmultiples_ι_iff W).mpr hm
        rw [hψ, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).mp hk, _root_.map_zero]
      · rw [hg_nmem x y h hm, ι_some]
        have hmb : (ι (K := L) W (.some x y h) : Wb.toAffine.Point) ∉ AddSubgroup.zmultiples Qb :=
          fun hh => hm ((mem_zmultiples_ι_iff W).mp hh)
        rw [ι_some] at hmb ⊢
        obtain ⟨h', hφ⟩ := hcoordb (algebraMap F L x) (algebraMap F L y) _ hmb
        rw [hψ, AddMonoidHom.comp_apply, hφ]
        show _ = pointCongr hVQ _
        rw [pointCongr_some]
        congr 1
        · rw [hSbS, map_veluX]
        · rw [hSbS, map_veluY]

  have hadd : ∀ P R, g (P + R) = g P + g R := by
    intro P R
    apply ι_injective (K := L) (W.veluQuotient S)
    rw [_root_.map_add, hkey, hkey, hkey, _root_.map_add, _root_.map_add]
  let φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point :=
    { toFun := g, map_zero' := hg_zero, map_add' := hadd }
  refine ⟨φ, ?_, ?_⟩
  · ext P
    rw [AddMonoidHom.mem_ker]
    show g P = 0 ↔ _
    constructor
    · intro h0
      have hk0 := hkey P
      rw [h0, _root_.map_zero] at hk0
      have hk : ι (K := L) W P ∈ φb.ker := by
        rw [AddMonoidHom.mem_ker]
        have h1 := hk0.symm
        rw [hψ, AddMonoidHom.comp_apply] at h1
        exact (pointCongr hVQ).map_eq_zero_iff.mp h1
      rw [hkerb] at hk
      exact (mem_zmultiples_ι_iff W).mp hk
    · intro hm
      rcases P with _ | ⟨x, y, h⟩
      · rfl
      · exact hg_mem x y h hm
  · intro x y h hm
    exact ⟨hns x y h hm, hg_nmem x y h hm⟩

end S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom
end P2MW
export P2MW.S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_ringHom (solution)
