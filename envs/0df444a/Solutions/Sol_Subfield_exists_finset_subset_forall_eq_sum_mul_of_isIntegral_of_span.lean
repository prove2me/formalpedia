-- Prove2me | solution 1 for Subfield.exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b5c60ddf-b6ac-5faf-95b2-d8ea687d30f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section
namespace L2FinCore
variable {Ω : Type*} [Field Ω]

def intClosureIn (R : Subring Ω) (F : Subfield Ω) : Subring Ω where
  carrier := {x | x ∈ F ∧ IsIntegral ↥R x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩

theorem mem_intClosureIn {R : Subring Ω} {F : Subfield Ω} {x : Ω} :
    x ∈ intClosureIn R F ↔ x ∈ F ∧ IsIntegral ↥R x := Iff.rfl

end L2FinCore
end

open L2FinCore in
set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 3200000 in
theorem solution
    {Ω : Type*} [Field Ω] [CharZero Ω]
    (R : Subring Ω) (hR : IsNoetherianRing ↥R)
    (F₀ L : Subfield Ω) (hRF : R ≤ F₀.toSubring) (hFL : F₀ ≤ L)
    (hfrac : ∀ x ∈ F₀, ∃ r ∈ R, ∃ d ∈ R, d ≠ 0 ∧ x * d = r)
    (N B : Set Ω) (hN : ∀ x, x ∈ N ↔ x ∈ F₀ ∧ IsIntegral ↥R x) (hB : ∀ x, x ∈ B ↔ x ∈ L ∧ IsIntegral ↥R x)
    (s : Finset Ω) (hs : ∀ x ∈ N, x ∈ Submodule.span ↥R (↑s : Set Ω))
    (u : Finset Ω) (hu : ∀ x ∈ L, x ∈ Submodule.span ↥F₀ (↑u : Set Ω)) :
    ∃ t : Finset Ω, (↑t : Set Ω) ⊆ B ∧
      ∀ x ∈ B, ∃ f : Ω → Ω, (∀ c ∈ t, f c ∈ N) ∧ x = ∑ c ∈ t, f c * c := by
  classical
  haveI := hR

  let N' : Subring Ω := intClosureIn R F₀
  let B' : Subring Ω := intClosureIn R L
  have hNN' : ∀ x, x ∈ N ↔ x ∈ N' := fun x => hN x
  have hBB' : ∀ x, x ∈ B ↔ x ∈ B' := fun x => hB x
  have hFL' : F₀.toSubring ≤ L.toSubring := hFL
  have hRN : R ≤ N' := fun x hx => ⟨hRF hx, isIntegral_algebraMap (R := ↥R) (A := Ω) (x := ⟨x, hx⟩)⟩
  have hNF : N' ≤ F₀.toSubring := fun _ hx => hx.1
  have hNB : N' ≤ B' := fun _ hx => ⟨hFL hx.1, hx.2⟩
  have hBL : B' ≤ L.toSubring := fun _ hx => hx.1

  letI iRN : Algebra ↥R ↥N' := (Subring.inclusion hRN).toAlgebra
  letI iNF : Algebra ↥N' ↥F₀ := (Subring.inclusion hNF).toAlgebra
  letI iNB : Algebra ↥N' ↥B' := (Subring.inclusion hNB).toAlgebra
  letI iBL : Algebra ↥B' ↥L := (Subring.inclusion hBL).toAlgebra
  letI iFL : Algebra ↥F₀ ↥L := (Subring.inclusion hFL').toAlgebra
  letI iNL : Algebra ↥N' ↥L := (Subring.inclusion (hNF.trans hFL')).toAlgebra
  letI iRL : Algebra ↥R ↥L := (Subring.inclusion (hRF.trans hFL')).toAlgebra
  haveI : IsScalarTower ↥N' ↥F₀ ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥N' ↥B' ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥R ↥N' ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tRNΩ : IsScalarTower ↥R ↥N' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tRLΩ : IsScalarTower ↥R ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tNLΩ : IsScalarTower ↥N' ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tNFΩ : IsScalarTower ↥N' ↥F₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tFLΩ : IsScalarTower ↥F₀ ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have intN_L : ∀ x : ↥L, IsIntegral ↥N' x ↔ IsIntegral ↥N' (x : Ω) := fun x =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥N' ↥L Ω) Subtype.val_injective).symm
  have intN_F : ∀ x : ↥F₀, IsIntegral ↥N' x ↔ IsIntegral ↥N' (x : Ω) := fun x =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥N' ↥F₀ Ω) Subtype.val_injective).symm

  haveI hNint : Algebra.IsIntegral ↥R ↥N' := ⟨fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥R ↥N' Ω) Subtype.val_injective).mp y.2.2⟩
  have intR_of_intN : ∀ x : Ω, IsIntegral ↥N' x → IsIntegral ↥R x := fun x hx => isIntegral_trans x hx
  have intN_of_intR : ∀ x : Ω, IsIntegral ↥R x → IsIntegral ↥N' x := fun x hx => hx.tower_top

  haveI hNfin : Module.Finite ↥R ↥N' := by
    let M : Submodule ↥R Ω := Submodule.span ↥R (↑s : Set Ω)
    haveI : IsNoetherian ↥R ↥M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span s.finite_toSet)
    let ι : ↥N' →ₗ[↥R] ↥M :=
      { toFun := fun x => ⟨(x : Ω), hs x ((hNN' x).mpr x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (show (x : Ω) = y from congrArg (fun m : ↥M => (m : Ω)) h)
    exact Module.Finite.of_injective ι hι
  haveI hNnoeth : IsNoetherianRing ↥N' := by
    haveI : Algebra.FiniteType ↥R ↥N' := Module.Finite.finiteType ↥N'
    exact Algebra.FiniteType.isNoetherianRing ↥R ↥N'

  haveI hNF₀ : IsFractionRing ↥N' ↥F₀ := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨y, hy⟩
      have hy0 : (algebraMap ↥N' ↥F₀ y) ≠ 0 := by
        intro h
        apply nonZeroDivisors.ne_zero hy
        exact Subtype.ext (show (y : Ω) = 0 from congrArg (fun z : ↥F₀ => (z : Ω)) h)
      exact isUnit_iff_ne_zero.mpr hy0
    · rintro ⟨z, hz⟩
      obtain ⟨r, hr, d, hd, hd0, hzd⟩ := hfrac z hz
      refine ⟨(⟨r, hRN hr⟩, ⟨⟨d, hRN hd⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hd0 (congrArg Subtype.val h))⟩), ?_⟩
      exact Subtype.ext hzd
    · intro x y h
      have hxy : x = y := Subtype.ext (show (x : Ω) = y from congrArg (fun z : ↥F₀ => (z : Ω)) h)
      exact ⟨1, by rw [hxy]⟩

  haveI hNic : IsIntegrallyClosed ↥N' := by
    refine (isIntegrallyClosed_iff ↥F₀).mpr fun {x} hx => ?_
    exact ⟨⟨(x : Ω), x.2, intR_of_intN _ ((intN_F x).mp hx)⟩, rfl⟩

  haveI hLfin : Module.Finite ↥F₀ ↥L := by
    let M : Submodule ↥F₀ Ω := Submodule.span ↥F₀ (↑u : Set Ω)
    haveI : IsNoetherian ↥F₀ ↥M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span u.finite_toSet)
    let ι : ↥L →ₗ[↥F₀] ↥M :=
      { toFun := fun x => ⟨(x : Ω), hu x x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun x y h =>
      Subtype.ext (show (x : Ω) = y from congrArg (fun m : ↥M => (m : Ω)) h)
    exact Module.Finite.of_injective ι hι
  haveI : CharZero ↥F₀ := (algebraMap ↥F₀ Ω).charZero
  haveI : Algebra.IsSeparable ↥F₀ ↥L := Algebra.IsAlgebraic.isSeparable_of_perfectField

  haveI hBic : IsIntegralClosure ↥B' ↥N' ↥L :=
    { algebraMap_injective := fun x y h =>
        Subtype.ext (show (x : Ω) = y from congrArg (fun z : ↥L => (z : Ω)) h)
      isIntegral_iff := fun {x} => by
        constructor
        · intro hx
          exact ⟨⟨(x : Ω), x.2, intR_of_intN _ ((intN_L x).mp hx)⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (intN_L _).mpr (intN_of_intR _ y.2.2) }

  haveI hBfin : Module.Finite ↥N' ↥B' := IsIntegralClosure.finite ↥N' ↥F₀ ↥L ↥B'

  obtain ⟨t₀, ht₀⟩ := hBfin.fg_top
  let val : ↥B' →ₗ[↥N'] Ω :=
    { toFun := fun c => (c : Ω)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let t : Finset Ω := Finset.image (fun c : ↥B' => ((c : ↥B') : Ω)) t₀
  refine ⟨t, ?_, ?_⟩
  · intro c hc
    obtain ⟨b, -, hbc⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
    rw [← hbc]
    exact (hBB' _).mpr b.2
  · intro x hxB
    have hxB' : x ∈ B' := (hBB' x).mp hxB
    have hmem : (⟨x, hxB'⟩ : ↥B') ∈ Submodule.span ↥N' (↑t₀ : Set ↥B') := by
      rw [ht₀]; exact Submodule.mem_top
    have himg := Submodule.mem_map_of_mem (f := val) hmem
    rw [Submodule.map_span] at himg
    have hsub : (val '' (↑t₀ : Set ↥B')) ⊆ (↑t : Set Ω) := by
      rintro _ ⟨b, hb, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, Finset.mem_coe.mp hb, rfl⟩)
    have hx' : x ∈ Submodule.span ↥N' (↑t : Set Ω) := Submodule.span_mono hsub himg
    obtain ⟨f₀, hf₀⟩ := Submodule.mem_span_finset.mp hx'
    have hsum : ∑ i ∈ t, f₀ i • i = x := by
      first
        | exact hf₀.2
        | exact hf₀
    refine ⟨fun c => ((f₀ c : ↥N') : Ω), fun c _ => (hNN' _).mpr (f₀ c).2, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact Algebra.smul_def (f₀ c) c

end S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span
end P2MW
export P2MW.S_Subfield_exists_finset_subset_forall_eq_sum_mul_of_isIntegral_of_span (solution)
