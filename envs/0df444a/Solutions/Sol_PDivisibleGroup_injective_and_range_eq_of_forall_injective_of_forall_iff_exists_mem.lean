-- Prove2me | solution 1 for PDivisibleGroup.injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/26b1b3bf-6699-5f8f-a644-abfc4339b253

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem

set_option autoImplicit false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
set_option Elab.async false

noncomputable section

namespace Ws47
namespace IMG

open PDivisibleGroup

variable {R : Type} [CommRing R] {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [Algebra R L]
variable {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
variable (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)

def lv (v : ℕ) (g : Γ.Point L v) : G.Point L v :=
  Point.ofAlgHom ((Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v))

theorem toAlgHom_lv (v : ℕ) (g : Γ.Point L v) :
    Point.toAlgHom (lv G Γ φ v g) = (Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v) := rfl

theorem lv_eq_convComp (v : ℕ) (g : Γ.Point L v) :
    lv G Γ φ v g = Point.ofConv (Hopf.convCompMonoidHom L (φ v) (Point.toConv g)) := rfl

theorem lv_mul (v : ℕ) (g g' : Γ.Point L v) : lv G Γ φ v (g * g') = lv G Γ φ v g * lv G Γ φ v g' := by
  rw [lv_eq_convComp, lv_eq_convComp, lv_eq_convComp, Point.toConv_mul, map_mul, Point.ofConv_mul (G := G)]

theorem lv_one (v : ℕ) : lv G Γ φ v (1 : Γ.Point L v) = 1 := by
  have h := lv_mul G Γ φ v (1 : Γ.Point L v) 1
  rw [mul_one] at h
  exact mul_left_cancel (a := lv G Γ φ v (1 : Γ.Point L v)) (by rw [← h, mul_one])

theorem lv_pow (v : ℕ) (g : Γ.Point L v) (n : ℕ) : lv G Γ φ v (g ^ n) = lv G Γ φ v g ^ n := by
  rw [lv_eq_convComp, lv_eq_convComp, Point.toConv_pow, map_pow, Point.ofConv_pow (G := G)]

variable {G Γ φ} in

theorem lv_pointIncl (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (v : ℕ) (g : Γ.Point L v) :
    lv G Γ φ (v + 1) (Γ.pointIncl L v g) = G.pointIncl L v (lv G Γ φ v g) := by
  have key : Point.toAlgHom (lv G Γ φ (v + 1) (Γ.pointIncl L v g))
      = Point.toAlgHom (G.pointIncl L v (lv G Γ φ v g)) := by
    rw [toAlgHom_lv, toAlgHom_pointIncl, toAlgHom_pointIncl, toAlgHom_lv, AlgHom.comp_assoc, AlgHom.comp_assoc]
    congr 1
    have := congrArg (fun f : G.level (v + 1) →ₐc[R] Γ.level v => (f : G.level (v + 1) →ₐ[R] Γ.level v)) (hφ v)
    simpa using this.symm
  exact congrArg Point.ofAlgHom key

variable {G Γ φ}

omit [Fact (Nat.Prime p)] in

theorem exists_rep_of_nsmul_eq_zero (K : PDivisibleGroup R p h) (v : ℕ) (z : K.Points L)
    (hz : ((p ^ v : ℕ) : ℤ) • z = 0) : ∃ g : K.Point L v, K.pointsMkAdd L v (Additive.ofMul g) = z := by
  obtain ⟨w, x, rfl⟩ := Points.exists_mkAdd K z
  rcases le_total w v with hwv | hvw
  · exact ⟨K.pointInclLE L hwv x, K.pointsMkAdd_pointInclLE hwv x⟩
  · have hx : x ^ (p ^ v) = 1 := by
      refine (K.pointsMkAdd_eq_pointsMkAdd_iff (L := L) _ _).1 ?_
      rw [ofMul_pow, map_nsmul, ofMul_one, map_zero, ← natCast_zsmul]
      exact hz
    obtain ⟨g, hg⟩ := K.exists_pointInclLE_eq_of_pow_eq_one hvw x hx
    exact ⟨g, by rw [← hg, K.pointsMkAdd_pointInclLE]⟩

theorem exists_rep (K : PDivisibleGroup R p h) (x : TateModule p (K.Points L)) (v : ℕ) :
    ∃ g : K.Point L v, K.pointsMkAdd L v (Additive.ofMul g) = (x : ℕ → K.Points L) v :=
  exists_rep_of_nsmul_eq_zero K v _ (TateModule.torsion x v)

theorem main [IsAlgClosed L] [CharZero L]
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (lv G Γ φ w g)))
    (M : Submodule ℤ_[p] (TateModule p (G.Points L)))
    (hinj : ∀ v : ℕ, Function.Injective (lv G Γ φ v : Γ.Point L v → G.Point L v))
    (himg : ∀ (v : ℕ) (y : G.Point L v),
        (∃ g : Γ.Point L v, lv G Γ φ v g = y) ↔
          ∃ x ∈ M, G.pointsMkAdd L v (Additive.ofMul y) = (x : ℕ → G.Points L) v) :
    Function.Injective Tφ ∧ LinearMap.range Tφ = M := by

  have hker : ∀ x : TateModule p (Γ.Points L), Tφ x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext
    funext n
    obtain ⟨g, hg⟩ := exists_rep Γ x n
    have h1 := hTφ x n n g hg
    rw [hx] at h1
    have h2 : lv G Γ φ n g = 1 := by
      refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := L) _ _).1 ?_
      rw [← h1, ofMul_one, map_zero]; rfl
    rw [← lv_one G Γ φ n] at h2
    have hg1 : g = 1 := hinj n h2
    rw [← hg, hg1, ofMul_one, map_zero]; rfl
  refine ⟨fun x y hxy => ?_, le_antisymm ?_ ?_⟩
  · have : Tφ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker _ this)
  ·
    rintro y ⟨x, rfl⟩
    obtain ⟨b⟩ := PDivisibleGroup.nonempty_basis_tateModule_points G L
    haveI : Module.Finite ℤ_[p] (TateModule p (G.Points L)) := Module.Finite.of_basis b
    have hv : ∀ v : ℕ, Submodule.Quotient.mk (p := M) (Tφ x)
        ∈ (IsLocalRing.maximalIdeal ℤ_[p] ^ v • (⊤ : Submodule ℤ_[p] (TateModule p (G.Points L) ⧸ M))) := by
      intro v
      obtain ⟨g, hg⟩ := exists_rep Γ x v
      obtain ⟨m, hmM, hm⟩ := (himg v (lv G Γ φ v g)).1 ⟨g, rfl⟩
      have h0 : TateModule.proj p (G.Points L) v (Tφ x - m) = 0 := by
        rw [map_sub, TateModule.proj_apply, TateModule.proj_apply, hTφ x v v g hg, ← hm, sub_self]
      have h1 := (TateModule.proj_eq_zero_iff v _).1 h0
      have h2 : Submodule.Quotient.mk (p := M) (Tφ x - m) = Submodule.Quotient.mk (Tφ x) := by
        rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero M).2 hmM, sub_zero]
      rw [← h2]
      have h3 : M.mkQ (Tφ x - m) ∈ Submodule.map M.mkQ (IsLocalRing.maximalIdeal ℤ_[p] ^ v • ⊤) :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h3
      exact h3
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := TateModule p (G.Points L) ⧸ M)
      (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
    have : Submodule.Quotient.mk (p := M) (Tφ x) ∈ (⊥ : Submodule ℤ_[p] (TateModule p (G.Points L) ⧸ M)) := by
      rw [← hK, Submodule.mem_iInf]; exact hv
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at this
    exact this
  ·
    intro m hm
    have hrep : ∀ v : ℕ, ∃ g : Γ.Point L v,
        G.pointsMkAdd L v (Additive.ofMul (lv G Γ φ v g)) = (m : ℕ → G.Points L) v := by
      intro v
      obtain ⟨y, hy⟩ := exists_rep G m v
      obtain ⟨g, hg⟩ := (himg v y).2 ⟨m, hm, hy⟩
      exact ⟨g, by rw [hg, hy]⟩
    choose g hg using hrep
    have hcompat : ∀ v : ℕ, g (v + 1) ^ p = Γ.pointIncl L v (g v) := by
      intro v
      apply hinj (v + 1)
      rw [lv_pow, lv_pointIncl hφ]
      refine (G.pointsMkAdd_eq_pointsMkAdd_iff (L := L) _ _).1 ?_
      rw [ofMul_pow, map_nsmul, hg (v + 1), G.pointsMkAdd_pointIncl, hg v, ← natCast_zsmul]
      exact TateModule.compat m v
    let xf : ℕ → Γ.Points L := fun v => Γ.pointsMkAdd L v (Additive.ofMul (g v))
    have hxT : xf ∈ TateModule p (Γ.Points L) := by
      intro n
      refine ⟨?_, ?_⟩
      · show ((p ^ n : ℕ) : ℤ) • Γ.pointsMkAdd L n (Additive.ofMul (g n)) = 0
        rw [natCast_zsmul, ← map_nsmul, ← ofMul_pow, Point.pow_card_eq_one, ofMul_one, map_zero]
      · show ((p : ℕ) : ℤ) • Γ.pointsMkAdd L (n + 1) (Additive.ofMul (g (n + 1)))
          = Γ.pointsMkAdd L n (Additive.ofMul (g n))
        rw [natCast_zsmul, ← map_nsmul, ← ofMul_pow, hcompat n, Γ.pointsMkAdd_pointIncl]
    refine ⟨⟨xf, hxT⟩, ?_⟩
    apply Subtype.ext
    funext v
    rw [hTφ ⟨xf, hxT⟩ v v (g v) rfl, hg v]

end Ws47.IMG

end

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[R] Γ.level w)))))
    (M : Submodule ℤ_[p] (TateModule p (G.Points L)))
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points L)), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hinj : ∀ v : ℕ, Function.Injective (fun g : Γ.Point L v =>
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v)) :
          Γ.Point L v → G.Point L v))
    (himg : ∀ (v : ℕ) (y : G.Point L v),
        (∃ g : Γ.Point L v, PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v)) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd L v (Additive.ofMul y) = (x : ℕ → G.Points L) v) :
    Function.Injective Tφ ∧ LinearMap.range Tφ = M := by
  exact Ws47.IMG.main (G := G) (Γ := Γ) (φ := φ) hφ Tφ hTφ M hinj himg

end S_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem
end P2MW
export P2MW.S_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem (solution)
