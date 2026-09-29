-- Prove2me | solution 1 for TateModule.natCard_primaryComponent_ker_eq_pow_valuation_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7edce721-39ec-54af-beb6-2f6f50e12367

import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_PadicInt_natCard_quotient_range_eq_pow_valuation_det
import Theorems.Thm_TateModule_nonempty_basis_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
set_option autoImplicit false

namespace PDAux2K3

open TateModule Submodule

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] {r : ℕ}
variable (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
variable (α : M →+ M)

include hcard in

theorem finite_torsionBy_of_card (n : ℕ) : Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

omit [Fact p.Prime] in

theorem α_mem_torsionBy {n : ℕ} {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    α m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := by
  rw [mem_torsionBy_iff] at hm ⊢
  rw [← α.map_zsmul, hm, map_zero]

def αRes (n : ℕ) : torsionBy ℤ M ((p ^ n : ℕ) : ℤ) →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) where
  toFun x := ⟨α (x : M), α_mem_torsionBy α x.2⟩
  map_zero' := Subtype.ext (by show α (0 : M) = 0; exact map_zero α)
  map_add' x y := Subtype.ext (by show α ((x : M) + (y : M)) = α (x : M) + α (y : M)
                                  exact map_add α (x : M) (y : M))

theorem proj_rep_apply (n : ℕ) (x : TateModule p M) :
    proj p M n (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap x) = α (proj p M n x) := by
  rfl

theorem natCard_ker_eq_natCard_coker {G : Type*} [AddCommGroup G] [Finite G] (β : G →+ G) :
    Nat.card β.ker = Nat.card (G ⧸ β.range) := by
  have h1 : Nat.card β.ker * Nat.card β.range = Nat.card G := by
    rw [mul_comm, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange β).toEquiv,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.ker]
  have h2 : Nat.card (G ⧸ β.range) * Nat.card β.range = Nat.card G :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.range).symm
  have hr : Nat.card (β.range : AddSubgroup G) ≠ 0 := Nat.card_pos.ne'
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr) (h1.trans h2.symm)

noncomputable def pnEnd (n : ℕ) : Module.End ℤ_[p] (TateModule p M) :=
  ((p : ℤ_[p]) ^ n) • (1 : Module.End ℤ_[p] (TateModule p M))

theorem range_pnEnd_eq (n : ℕ) :
    LinearMap.range (pnEnd (p := p) (M := M) n) =
      (IsLocalRing.maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] (TateModule p M)) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]
  ext x
  simp only [pnEnd, LinearMap.mem_range, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

theorem det_pnEnd_eq (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (n : ℕ) :
    LinearMap.det (pnEnd (p := p) (M := M) n) = (p : ℤ_[p]) ^ (n * r) := by
  haveI : Module.Free ℤ_[p] (TateModule p M) := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[p] (TateModule p M) := Module.Finite.of_basis b
  rw [pnEnd, LinearMap.det_smul, show (1 : Module.End ℤ_[p] (TateModule p M)) = LinearMap.id from rfl,
    LinearMap.det_id, mul_one, Module.finrank_eq_card_basis b, Fintype.card_fin, ← pow_mul]

theorem det_pnEnd_ne_zero (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (n : ℕ) :
    LinearMap.det (pnEnd (p := p) (M := M) n) ≠ 0 := by
  rw [det_pnEnd_eq b]
  exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

theorem natCard_tate_quot_pn (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (n : ℕ) :
    Nat.card (TateModule p M ⧸
      ((IsLocalRing.maximalIdeal ℤ_[p] ^ n) • (⊤ : Submodule ℤ_[p] (TateModule p M))))
      = (p ^ n) ^ r := by
  haveI : Module.Free ℤ_[p] (TateModule p M) := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[p] (TateModule p M) := Module.Finite.of_basis b
  rw [← range_pnEnd_eq,
    PadicInt.natCard_quotient_range_eq_pow_valuation_det p _ (det_pnEnd_ne_zero b n),
    det_pnEnd_eq b, PadicInt.valuation_pow, PadicInt.valuation_p, mul_one, ← pow_mul,
    mul_comm n r, pow_mul]

include hcard in

theorem range_proj_eq_torsionBy (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (n : ℕ) :
    (proj p M n).range = (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)).toAddSubgroup := by

  haveI hFinLev := finite_torsionBy_of_card hcard (p := p) (M := M) n
  have hker : (proj p M n).ker =
      ((IsLocalRing.maximalIdeal ℤ_[p] ^ n) •
        (⊤ : Submodule ℤ_[p] (TateModule p M))).toAddSubgroup := by
    ext x; rw [AddMonoidHom.mem_ker, proj_eq_zero_iff]; rfl
  have hcard_range : Nat.card (proj p M n).range = (p ^ n) ^ r := by
    have e := (QuotientAddGroup.quotientKerEquivRange (proj p M n)).toEquiv
    rw [← Nat.card_congr e, hker]
    have e2 : (TateModule p M ⧸ ((IsLocalRing.maximalIdeal ℤ_[p] ^ n) •
          (⊤ : Submodule ℤ_[p] (TateModule p M))).toAddSubgroup) ≃
        (TateModule p M ⧸ ((IsLocalRing.maximalIdeal ℤ_[p] ^ n) •
          (⊤ : Submodule ℤ_[p] (TateModule p M)))) :=
      (QuotientAddGroup.quotientAddEquivOfEq rfl).toEquiv
    rw [Nat.card_congr e2]
    exact natCard_tate_quot_pn b n

  haveI hFinRange : Finite ((proj p M n).range) :=
    Nat.finite_of_card_ne_zero
      (hcard_range ▸ pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  refine (SetLike.coe_set_eq (p := (proj p M n).range)
    (q := (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)).toAddSubgroup)).mp ?_
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · rintro x ⟨y, rfl⟩; exact proj_mem_torsionBy n y
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      show Nat.card ↑(((torsionBy ℤ M ((p ^ n : ℕ) : ℤ)).toAddSubgroup : AddSubgroup M) : Set M) =
        Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) from rfl,
      hcard n,
      show Nat.card ↑(((proj p M n).range : AddSubgroup M) : Set M) =
        Nat.card (proj p M n).range from rfl, hcard_range]

theorem pow_smul_mem_range
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (f : Module.End ℤ_[p] (TateModule p M)) (hf : LinearMap.det f ≠ 0) (x : TateModule p M) :
    ((p : ℤ_[p]) ^ (LinearMap.det f).valuation) • x ∈ LinearMap.range f := by
  haveI : Module.Free ℤ_[p] (TateModule p M) := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[p] (TateModule p M) := Module.Finite.of_basis b
  have hK2 : Nat.card (TateModule p M ⧸ LinearMap.range f) = p ^ (LinearMap.det f).valuation :=
    PadicInt.natCard_quotient_range_eq_pow_valuation_det p f hf
  haveI hFin : Finite (TateModule p M ⧸ LinearMap.range f) :=
    Nat.finite_of_card_ne_zero (by rw [hK2]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  haveI := Fintype.ofFinite (TateModule p M ⧸ LinearMap.range f)
  have hLag : Nat.card (TateModule p M ⧸ LinearMap.range f) •
      ((LinearMap.range f).mkQ x : TateModule p M ⧸ LinearMap.range f) = 0 := by
    rw [Nat.card_eq_fintype_card]; exact card_nsmul_eq_zero
  rw [hK2, ← map_nsmul] at hLag
  have hmem : (p ^ (LinearMap.det f).valuation : ℕ) • x ∈ LinearMap.range f :=
    (Submodule.Quotient.mk_eq_zero _).mp hLag
  have hcast : ((p : ℤ_[p]) ^ (LinearMap.det f).valuation) • x =
      ((p ^ (LinearMap.det f).valuation : ℕ) : ℤ_[p]) • x := by push_cast; ring_nf
  rw [hcast, Nat.cast_smul_eq_nsmul]
  exact hmem

def projTors (n : ℕ) : TateModule p M →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) where
  toFun x := ⟨proj p M n x, proj_mem_torsionBy n x⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

omit [Fact p.Prime] in
theorem projTors_coe (n : ℕ) (x : TateModule p M) : (projTors n x : M) = proj p M n x := rfl

include hcard in
theorem projTors_surjective (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M)) (n : ℕ) :
    Function.Surjective (projTors (p := p) (M := M) n) := by
  intro ⟨m, hm⟩
  have := (range_proj_eq_torsionBy hcard b n).ge hm
  obtain ⟨x, hx⟩ := this
  exact ⟨x, Subtype.ext hx⟩

theorem αRes_projTors (n : ℕ) (x : TateModule p M) :
    αRes α n (projTors n x) =
      projTors n (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap x) :=
  Subtype.ext (proj_rep_apply α n x).symm

theorem pn_smul_mem_range
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (f : Module.End ℤ_[p] (TateModule p M)) (hf : LinearMap.det f ≠ 0) (n : ℕ)
    (hn : (LinearMap.det f).valuation ≤ n) (x : TateModule p M) :
    ((p : ℤ_[p]) ^ n) • x ∈ LinearMap.range f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add, mul_smul]
  exact pow_smul_mem_range b f hf _

include hcard in

theorem natCard_quotient_αRes_range_eq
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0)
    (n : ℕ)
    (hn : (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation ≤ n) :
    Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ) ⧸ (αRes α n).range) =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by
  haveI : Module.Free ℤ_[p] (TateModule p M) := Module.Free.of_basis b
  haveI : Module.Finite ℤ_[p] (TateModule p M) := Module.Finite.of_basis b
  set f := TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap with hfdef

  let π : TateModule p M →+ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) ⧸ (αRes α n).range :=
    (QuotientAddGroup.mk' (αRes α n).range).comp (projTors n)
  have hπsurj : Function.Surjective π := (QuotientAddGroup.mk'_surjective _).comp
    (projTors_surjective hcard b n)

  have hπker : π.ker = (LinearMap.range f).toAddSubgroup := by
    ext x
    simp only [π, AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨⟨y, hy⟩, heq⟩

      obtain ⟨z, hz⟩ := projTors_surjective hcard b n ⟨y, hy⟩
      have hαy : projTors n (f z) = projTors n x := by
        rw [← αRes_projTors α n z, hz]; exact heq
      have hdiff : proj p M n (x - f z) = 0 := by
        rw [map_sub, ← projTors_coe, ← projTors_coe, hαy, sub_self]
      rw [proj_eq_zero_iff] at hdiff
      obtain ⟨w, hw⟩ : ∃ w, x - f z = (p : ℤ_[p]) ^ n • w := by
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
          Submodule.ideal_span_singleton_smul] at hdiff
        obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hdiff
        exact ⟨w, hw.symm⟩
      rw [show x = f z + (p : ℤ_[p]) ^ n • w from by rw [← hw]; abel]
      exact (LinearMap.range f).add_mem (LinearMap.mem_range_self f z)
        (pn_smul_mem_range b f hdet n hn w)
    · rintro ⟨z, rfl⟩
      exact ⟨projTors n z, αRes_projTors α n z⟩

  have e : (TateModule p M ⧸ π.ker) ≃+
      torsionBy ℤ M ((p ^ n : ℕ) : ℤ) ⧸ (αRes α n).range :=
    QuotientAddGroup.quotientKerEquivOfSurjective π hπsurj
  rw [← Nat.card_congr e.toEquiv, hπker]
  have e2 : (TateModule p M ⧸ (LinearMap.range f).toAddSubgroup) ≃
      (TateModule p M ⧸ LinearMap.range f) :=
    (QuotientAddGroup.quotientAddEquivOfEq rfl).toEquiv
  rw [Nat.card_congr e2]
  exact PadicInt.natCard_quotient_range_eq_pow_valuation_det p f hdet

omit [Fact p.Prime] in

theorem mem_primaryComponent_ker_iff (x : α.ker) :
    x ∈ AddCommGroup.primaryComponent α.ker p ↔
      ∃ n : ℕ, (x : M) ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := by
  rw [AddCommGroup.mem_primaryComponent]
  refine ⟨fun ⟨k, hk⟩ => ⟨k, ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  · rw [mem_torsionBy_iff]
    have : ((p ^ k : ℕ) • x : α.ker) = 0 := hk
    calc ((p ^ k : ℕ) : ℤ) • (x : M) = ((p ^ k : ℕ) • x : α.ker) := by
          rw [natCast_zsmul]; rfl
      _ = 0 := by rw [this]; rfl
  · rw [mem_torsionBy_iff] at hn
    ext
    show (p ^ n : ℕ) • (x : M) = 0
    rw [← natCast_zsmul]
    exact_mod_cast hn

omit [Fact p.Prime] in

theorem torsionBy_mono {m n : ℕ} (hmn : m ≤ n) :
    torsionBy ℤ M ((p ^ m : ℕ) : ℤ) ≤ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro x hx
  rw [mem_torsionBy_iff] at hx ⊢
  rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, hx, smul_zero]

def kerResLift {m n : ℕ} (hmn : m ≤ n) :
    (αRes (p := p) α m).ker → (αRes (p := p) α n).ker :=
  fun x => ⟨⟨(x : M), torsionBy_mono (p := p) hmn (x : torsionBy ℤ M ((p ^ m : ℕ) : ℤ)).2⟩,
    by
      rw [AddMonoidHom.mem_ker]
      ext
      have hx0 : α (x : M) = 0 := congrArg Subtype.val x.2
      exact hx0⟩

omit [Fact p.Prime] in
theorem kerResLift_injective {m n : ℕ} (hmn : m ≤ n) :
    Function.Injective (kerResLift (p := p) α hmn) := fun x y h => by
  rcases x with ⟨⟨xv, _⟩, _⟩; rcases y with ⟨⟨yv, _⟩, _⟩
  simpa [kerResLift, Subtype.ext_iff] using h

include hcard in

theorem natCard_ker_αRes_eq
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0)
    (n : ℕ)
    (hn : (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation ≤ n) :
    Nat.card (αRes (p := p) α n).ker =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by
  haveI := finite_torsionBy_of_card hcard (p := p) (M := M) n
  rw [natCard_ker_eq_natCard_coker (αRes (p := p) α n)]
  exact natCard_quotient_αRes_range_eq hcard α b hdet n hn

include hcard in

theorem primComp_mem_torsionBy_v
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0)
    (x : α.ker) (hx : x ∈ AddCommGroup.primaryComponent α.ker p) :
    (x : M) ∈ torsionBy ℤ M
      ((p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M)
        α.toIntLinearMap)).valuation : ℕ) : ℤ) := by
  set v := (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation
  obtain ⟨k, hk⟩ := (mem_primaryComponent_ker_iff α x).mp hx
  let n := max k v
  have hxn : (x : M) ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
    torsionBy_mono (p := p) (le_max_left k v) hk

  let xn : (αRes (p := p) α n).ker := ⟨⟨(x : M), hxn⟩, by
    rw [AddMonoidHom.mem_ker]; ext
    exact (AddMonoidHom.mem_ker.mp x.2 : α (x : M) = 0)⟩
  haveI hFinN := finite_torsionBy_of_card hcard (p := p) (M := M) n
  haveI hFinV := finite_torsionBy_of_card hcard (p := p) (M := M) v
  haveI : Finite (αRes (p := p) α n).ker := Subtype.finite
  haveI : Finite (αRes (p := p) α v).ker := Subtype.finite

  have hcardV := natCard_ker_αRes_eq hcard α b hdet v le_rfl
  have hcardN := natCard_ker_αRes_eq hcard α b hdet n (le_max_right _ _)
  have hbij : Function.Bijective (kerResLift (p := p) α (le_max_right k v : v ≤ n)) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨kerResLift_injective α _, by rw [hcardV, hcardN]⟩
  obtain ⟨y, hy⟩ := hbij.surjective xn
  have hyM : (y : M) = (x : M) := Subtype.ext_iff.mp (Subtype.ext_iff.mp hy)
  rw [← hyM]
  exact (y : torsionBy ℤ M ((p ^ v : ℕ) : ℤ)).2

include hcard in

theorem natCard_primaryComponent_eq
    (b : Module.Basis (Fin r) ℤ_[p] (TateModule p M))
    (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0) :
    Nat.card (AddCommGroup.primaryComponent α.ker p) =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by
  set v := (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation
    with hvdef
  haveI hFinV := finite_torsionBy_of_card hcard (p := p) (M := M) v
  haveI : Finite (αRes (p := p) α v).ker := Subtype.finite

  let toKer : AddCommGroup.primaryComponent α.ker p → (αRes (p := p) α v).ker := fun x =>
    ⟨⟨((x : α.ker) : M), primComp_mem_torsionBy_v hcard α b hdet x x.2⟩,
      by rw [AddMonoidHom.mem_ker]; ext
         exact (AddMonoidHom.mem_ker.mp (x : α.ker).2 : α ((x : α.ker) : M) = 0)⟩
  let fromKer : (αRes (p := p) α v).ker → AddCommGroup.primaryComponent α.ker p := fun y =>
    ⟨⟨(y : M), by
        rw [AddMonoidHom.mem_ker]
        have hy0 : αRes (p := p) α v (y : torsionBy ℤ M ((p ^ v : ℕ) : ℤ)) = 0 := y.2
        exact congrArg Subtype.val hy0⟩,
      (mem_primaryComponent_ker_iff α _).mpr
        ⟨v, (y : torsionBy ℤ M ((p ^ v : ℕ) : ℤ)).2⟩⟩
  have hLI : Function.LeftInverse fromKer toKer := fun x => by
    rcases x with ⟨⟨xv, _⟩, _⟩; rfl
  have hRI : Function.RightInverse fromKer toKer := fun y => by
    rcases y with ⟨⟨yv, _⟩, _⟩; rfl
  rw [Nat.card_eq_of_bijective toKer ⟨hLI.injective, hRI.surjective⟩]
  exact natCard_ker_αRes_eq hcard α b hdet v le_rfl

end PDAux2K3

open PDAux2K3 in
theorem solution (p : ℕ) [Fact p.Prime] {M : Type}
    [AddCommGroup M] (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (α : M →+ M) (hdet : LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap) ≠ 0) :
    Nat.card (AddCommGroup.primaryComponent α.ker p) =
      p ^ (LinearMap.det (TateModule.rep p M (Module.End ℤ M) α.toIntLinearMap)).valuation := by
  obtain ⟨b⟩ := TateModule.nonempty_basis_of_card_torsionBy p r hcard
  exact natCard_primaryComponent_eq hcard α b hdet

#print axioms solution

end S_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det
end P2MW
export P2MW.S_TateModule_natCard_primaryComponent_ker_eq_pow_valuation_det (solution)
