-- Prove2me | solution 1 for TateModule.exists_basis_span_eq_of_filtration
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2f843450-f8c2-5518-92c9-10d834a4d80c

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateModule_exists_basis_span_eq_of_filtration

open IsLocalRing Submodule Module

namespace TateModule
p2m_export "TateModule" "torsion coe_add coe_zero toZModPow_eq_appr smul_apply proj_apply proj_mem_torsionBy smul_eq_zero_of_mem_torsionBy_one finite_torsionBy proj_surjective dvd_of_rel_apply linearIndependent_pair mem_span_pair top_le_span_pair free"
p2m_open "TateModule"

section FreeLine
variable {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
variable (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^2)
variable (F : ℕ → AddSubgroup M) (P : M → Prop)
variable (hFiff : ∀ m, 1 ≤ m → ∀ x, x ∈ F m ↔ ((p^m : ℕ) : ℤ) • x = 0 ∧ P x)
variable (hFcard : ∀ m, 1 ≤ m → Nat.card (F m) = p^m)

include hFiff

omit [Fact p.Prime] in
private theorem filt_tor {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : x ∈ F m) :
    ((p^m : ℕ) : ℤ) • x = 0 :=
  ((hFiff m hm x).1 hx).1

omit [Fact p.Prime] in
private theorem filt_pred {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : x ∈ F m) : P x :=
  ((hFiff m hm x).1 hx).2

omit [Fact p.Prime] in
private theorem filt_mem {m : ℕ} (hm : 1 ≤ m) {x : M}
    (htor : ((p^m : ℕ) : ℤ) • x = 0) (hP : P x) : x ∈ F m :=
  (hFiff m hm x).2 ⟨htor, hP⟩

omit [Fact p.Prime] in
private theorem filt_down {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : x ∈ F (m+1)) :
    ((p : ℕ) : ℤ) • x ∈ F m := by
  have hx' : ((p : ℕ) : ℤ) • x ∈ F (m+1) := (F (m+1)).zsmul_mem hx _
  refine filt_mem F P hFiff hm ?_ (filt_pred F P hFiff (by omega) hx')
  rw [smul_smul, ← Nat.cast_mul, ← pow_succ]
  exact filt_tor F P hFiff (by omega) hx

omit [Fact p.Prime] in
private theorem filt_one_iff {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : x ∈ F m) :
    x ∈ F 1 ↔ ((p : ℕ) : ℤ) • x = 0 := by
  constructor
  · intro h1
    have := filt_tor F P hFiff le_rfl h1
    rwa [pow_one] at this
  · intro hp
    refine filt_mem F P hFiff le_rfl ?_ (filt_pred F P hFiff hm hx)
    rwa [pow_one]

omit [Fact p.Prime] in
private theorem filt_mem_torsionBy {m : ℕ} (hm : 1 ≤ m) {x : M} (hx : x ∈ F m) :
    x ∈ torsionBy ℤ M ((p^m : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).2 (filt_tor F P hFiff hm hx)

include hcard in
private theorem filt_finite {m : ℕ} (hm : 1 ≤ m) : Finite (F m) := by
  haveI := finite_torsionBy hcard m
  refine Finite.of_injective (fun x : F m => (⟨x.1, filt_mem_torsionBy F P hFiff hm x.2⟩
    : torsionBy ℤ M ((p^m : ℕ) : ℤ))) (fun a b h => ?_)
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext h

private def filtMulP (m : ℕ) (hm : 1 ≤ m) : F (m+1) →+ F m where
  toFun x := ⟨((p : ℕ) : ℤ) • (x : M), filt_down F P hFiff hm x.2⟩
  map_zero' := Subtype.ext (smul_zero _)
  map_add' _ _ := Subtype.ext (smul_add _ _ _)

private noncomputable def filtMulP_ker_equiv (m : ℕ) (hm : 1 ≤ m) :
    (filtMulP F P hFiff m hm).ker ≃ F 1 := by
  refine Equiv.ofBijective (fun x => ⟨(x : F (m+1)).1,
    (filt_one_iff F P hFiff (by omega) x.1.2).2
      (congrArg Subtype.val (AddMonoidHom.mem_ker.1 x.2))⟩) ⟨?_, ?_⟩
  · intro a b h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  · intro y
    have hyone : ((p : ℕ) : ℤ) • (y : M) = 0 := by
      have := filt_tor F P hFiff le_rfl y.2
      rwa [pow_one] at this
    have hytor : ((p^(m+1) : ℕ) : ℤ) • (y : M) = 0 := by
      rw [pow_succ, Nat.cast_mul, mul_smul, hyone, smul_zero]
    have hyFm1 : (y : M) ∈ F (m+1) :=
      filt_mem F P hFiff (by omega) hytor (filt_pred F P hFiff le_rfl y.2)
    exact ⟨⟨⟨y, hyFm1⟩, AddMonoidHom.mem_ker.2 (Subtype.ext hyone)⟩, rfl⟩

include hcard hFcard in
private theorem filtMulP_surjective (m : ℕ) (hm : 1 ≤ m) :
    Function.Surjective (filtMulP F P hFiff m hm) := by
  haveI := filt_finite hcard F P hFiff hm
  haveI := filt_finite hcard F P hFiff (by omega : 1 ≤ m+1)
  rw [← AddMonoidHom.range_eq_top]
  refine AddSubgroup.eq_top_of_card_eq _ ?_
  have hker : Nat.card (filtMulP F P hFiff m hm).ker = p := by
    rw [Nat.card_congr (filtMulP_ker_equiv F P hFiff m hm), hFcard 1 le_rfl, pow_one]
  have hquo := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (filtMulP F P hFiff m hm).ker
  rw [hFcard (m+1) (by omega), Nat.card_congr
    (QuotientAddGroup.quotientKerEquivRange (filtMulP F P hFiff m hm)).toEquiv, hker] at hquo
  have hFm := hFcard m hm
  have hps : p ^ (m + 1) = p ^ m * p := pow_succ p m
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : Nat.card (filtMulP F P hFiff m hm).range * p = p ^ m * p := hps ▸ hquo.symm
  exact Nat.eq_of_mul_eq_mul_right hp this ▸ hFm.symm

include hcard hFcard in
private theorem filt_exists_smul_eq (m : ℕ) (hm : 1 ≤ m) {y : M} (hy : y ∈ F m) :
    ∃ x ∈ F (m+1), ((p : ℕ) : ℤ) • x = y := by
  obtain ⟨⟨x, hx⟩, hxy⟩ := filtMulP_surjective hcard F P hFiff hFcard m hm ⟨y, hy⟩
  exact ⟨x, hx, congrArg Subtype.val hxy⟩

include hcard hFcard in

private noncomputable def filtSeq (e : M) (he : e ∈ F 1) : (m : ℕ) → {x : M // x ∈ F (m+1)}
  | 0 => ⟨e, he⟩
  | m + 1 =>
    ⟨(filt_exists_smul_eq hcard F P hFiff hFcard (m+1) (by omega) (filtSeq e he m).2).choose,
     (filt_exists_smul_eq hcard F P hFiff hFcard (m+1) (by omega) (filtSeq e he m).2).choose_spec.1⟩

include hcard hFcard in
private theorem filtSeq_spec (e : M) (he : e ∈ F 1) (m : ℕ) :
    ((p : ℕ) : ℤ) • (filtSeq hcard F P hFiff hFcard e he (m+1) : M)
      = (filtSeq hcard F P hFiff hFcard e he m : M) :=
  (filt_exists_smul_eq hcard F P hFiff hFcard (m+1) (by omega)
    (filtSeq hcard F P hFiff hFcard e he m).2).choose_spec.2

include hcard hFcard in

private noncomputable def filtV (e : M) (he : e ∈ F 1) : TateModule p M :=
  ⟨fun m => match m with
    | 0 => 0
    | m + 1 => filtSeq hcard F P hFiff hFcard e he m,
   fun m => ⟨by
    match m with
    | 0 => simp
    | m + 1 => exact filt_tor F P hFiff (by omega) (filtSeq hcard F P hFiff hFcard e he m).2,
   by
    match m with
    | 0 =>
      show ((p : ℕ) : ℤ) • (filtSeq hcard F P hFiff hFcard e he 0 : M) = 0
      have := filt_tor F P hFiff le_rfl (filtSeq hcard F P hFiff hFcard e he 0).2
      rwa [pow_one] at this
    | m + 1 => exact filtSeq_spec hcard F P hFiff hFcard e he m⟩⟩

include hcard hFcard in
private theorem filtV_apply_succ (e : M) (he : e ∈ F 1) (m : ℕ) :
    (filtV hcard F P hFiff hFcard e he : ℕ → M) (m+1) = filtSeq hcard F P hFiff hFcard e he m := rfl

include hcard hFcard in
private theorem filtV_apply_one (e : M) (he : e ∈ F 1) :
    (filtV hcard F P hFiff hFcard e he : ℕ → M) 1 = e := rfl

include hcard hFcard in
private theorem filtV_mem_filt (e : M) (he : e ∈ F 1) (m : ℕ) (hm : 1 ≤ m) :
    (filtV hcard F P hFiff hFcard e he : ℕ → M) m ∈ F m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm]
  exact (filtSeq hcard F P hFiff hFcard e he k).2

include hcard hFcard in
private theorem filt_exists_ne_zero : ∃ e ∈ F 1, e ≠ 0 := by
  haveI := filt_finite hcard F P hFiff (le_refl 1)
  have h1 : Nat.card (F 1) = p := by rw [hFcard 1 le_rfl, pow_one]
  have hp : 1 < Nat.card (F 1) := h1 ▸ (Fact.out : p.Prime).one_lt
  haveI : Nontrivial (F 1) := Finite.one_lt_card_iff_nontrivial.mp hp
  obtain ⟨y, hy⟩ := exists_ne (0 : F 1)
  exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0)⟩

end FreeLine

private theorem exists_indep_of_ne_zero {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (hV : Nat.card V = p ^ 2) {v : V} (hv : v ≠ 0) :
    ∃ w : V, ∀ a b : ℤ, a • v + b • w = 0 → (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have hp : p.Prime := Fact.out
  have hrank : Module.finrank (ZMod p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have hspan : span (ZMod p) {v} ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank (ZMod p) (span (ZMod p) {v}) = 1 := finrank_span_singleton hv
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨w, -, hw⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hspan)
  refine ⟨w, fun a b hab => ?_⟩
  rw [← Int.cast_smul_eq_zsmul (ZMod p) a, ← Int.cast_smul_eq_zsmul (ZMod p) b] at hab
  by_cases hb : ((b : ℤ) : ZMod p) = 0
  · have ha : ((a : ℤ) : ZMod p) • v = 0 := by rwa [hb, zero_smul, add_zero] at hab
    have ha0 : ((a : ℤ) : ZMod p) = 0 := by
      rcases smul_eq_zero.mp ha with h | h
      · exact h
      · exact absurd h hv
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha0,
           (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩
  · exfalso
    apply hw
    have hbw : ((b : ℤ) : ZMod p) • w = -(((a : ℤ) : ZMod p) • v) :=
      eq_neg_of_add_eq_zero_right hab
    have hw' : w = (((b : ℤ) : ZMod p)⁻¹ * -((a : ℤ) : ZMod p)) • v := by
      calc w = ((b : ℤ) : ZMod p)⁻¹ • (((b : ℤ) : ZMod p) • w) := (inv_smul_smul₀ hb w).symm
        _ = ((b : ℤ) : ZMod p)⁻¹ • (-(((a : ℤ) : ZMod p) • v)) := by rw [hbw]
        _ = (((b : ℤ) : ZMod p)⁻¹ * -((a : ℤ) : ZMod p)) • v := by
            rw [mul_smul, neg_smul]
    rw [hw']
    exact smul_mem _ _ (mem_span_singleton_self v)

private theorem exists_indep_snd
    {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (v : TateModule p M) (hv : (v : ℕ → M) 1 ≠ 0) :
    ∃ w : TateModule p M,
      ∀ a b : ℤ, a • (v : ℕ → M) 1 + b • (w : ℕ → M) 1 = 0 → (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  haveI := finite_torsionBy hcard 1
  have hmod : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), p • m = 0 := fun m =>
    Subtype.ext (by
      rw [coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ, Submodule.coe_zero]
      exact smul_eq_zero_of_mem_torsionBy_one m.2)
  letI : Module (ZMod p) (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) := AddCommGroup.zmodModule hmod
  have h1card : Nat.card (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ 2 := by
    rw [hcard 1, pow_one]
  have hv1mem : (v : ℕ → M) 1 ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ) := by
    rw [← proj_apply]
    exact proj_mem_torsionBy 1 v
  obtain ⟨w₁, hw₁⟩ := exists_indep_of_ne_zero h1card
    (v := (⟨(v : ℕ → M) 1, hv1mem⟩ : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)))
    (fun h => hv (by simpa [Subtype.ext_iff] using h))
  obtain ⟨w, hw⟩ := proj_surjective hcard 1 (w₁ : M) w₁.2
  have hwcoe : (w₁ : M) = (w : ℕ → M) 1 := by
    rw [← hw]
    exact (proj_apply 1 w).symm
  refine ⟨w, fun a b hab => ?_⟩
  refine hw₁ a b (Subtype.ext ?_)
  rw [Submodule.coe_add, coe_smul_of_tower, coe_smul_of_tower, Submodule.coe_zero, hwcoe]
  exact hab

private theorem dvd_of_smul_mem_addSubgroup {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    {v w : TateModule p M}
    (h1 : ∀ a b : ℤ, a • (v : ℕ → M) 1 + b • (w : ℕ → M) 1 = 0 → (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b)
    {G : AddSubgroup M} {m : ℕ} [Finite G] (hGcard : Nat.card G = p ^ m)
    (hvG : (v : ℕ → M) m ∈ G)
    {c : ℤ} (hc : c • (w : ℕ → M) m ∈ G) : ((p^m : ℕ) : ℤ) ∣ c := by
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

  let f : ZMod (p^m) → G := fun a => ⟨(a.val : ℤ) • (v : ℕ → M) m, G.zsmul_mem hvG _⟩
  have hfinj : Function.Injective f := fun a b h => by
    have hab : ((a.val : ℤ) - b.val) • (v : ℕ → M) m + (0 : ℤ) • (w : ℕ → M) m = 0 := by
      have := congrArg Subtype.val h
      simp only [f] at this
      rw [zero_smul, add_zero, sub_smul, sub_eq_zero]; exact this
    have hdvd := (dvd_of_rel_apply h1 m _ _ hab).1
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (b.val : ℤ) (a.val : ℤ) (p ^ m)).mpr hdvd
    rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      eq_comm] at this
  have hfbij : Function.Bijective f := by
    refine hfinj.bijective_of_nat_card_le ?_
    rw [hGcard, Nat.card_zmod]

  obtain ⟨a, ha⟩ := hfbij.2 ⟨c • (w : ℕ → M) m, hc⟩
  have hac : (a.val : ℤ) • (v : ℕ → M) m + (-c) • (w : ℕ → M) m = 0 := by
    have := congrArg Subtype.val ha
    simp only [f] at this
    rw [neg_smul, this, add_neg_cancel]
  exact (dvd_neg.mp (dvd_of_rel_apply h1 m _ _ hac).2)

private theorem exists_basis_span_eq_of_filtration_aux
    {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^2)
    (F : ℕ → AddSubgroup M) (P : M → Prop)
    (hFiff : ∀ m, 1 ≤ m → ∀ x, x ∈ F m ↔ ((p^m : ℕ) : ℤ) • x = 0 ∧ P x)
    (hFcard : ∀ m, 1 ≤ m → Nat.card (F m) = p^m)
    (L : Submodule ℤ_[p] (TateModule p M))
    (hL : ∀ x, x ∈ L ↔ ∀ m, 1 ≤ m → (x : ℕ → M) m ∈ F m) :
    ∃ b : Module.Basis (Fin 2) ℤ_[p] (TateModule p M), L = ℤ_[p] ∙ b 0 := by

  obtain ⟨e, heF1, hene⟩ := filt_exists_ne_zero hcard F P hFiff hFcard
  set v₀ := filtV hcard F P hFiff hFcard e heF1 with hv₀def
  have hv₀1 : (v₀ : ℕ → M) 1 ≠ 0 := by
    rw [hv₀def, filtV_apply_one]; exact hene
  have hv₀F : ∀ m, 1 ≤ m → (v₀ : ℕ → M) m ∈ F m :=
    filtV_mem_filt hcard F P hFiff hFcard e heF1
  have hv₀L : v₀ ∈ L := (hL v₀).2 hv₀F

  obtain ⟨w, h1⟩ := exists_indep_snd hcard v₀ hv₀1
  let b : Module.Basis (Fin 2) ℤ_[p] (TateModule p M) :=
    Module.Basis.mk (v := ![v₀, w]) (linearIndependent_pair h1) (top_le_span_pair hcard h1)
  have hb0 : b 0 = v₀ := Module.Basis.mk_apply _ _ 0
  refine ⟨b, le_antisymm ?_ ?_⟩
  ·
    intro x hxL
    obtain ⟨s, t, hst⟩ := mem_span_pair hcard h1 x
    have htwL : t • w ∈ L := by
      have heq : t • w = x - s • v₀ := by rw [← hst]; abel
      rw [heq]; exact L.sub_mem hxL (L.smul_mem s hv₀L)
    have ht0 : t = 0 := by
      refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
      rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      haveI := filt_finite hcard F P hFiff hn
      have htwFn : ((t.appr n : ℕ) : ℤ) • (w : ℕ → M) n ∈ F n := by
        have := (hL (t • w)).1 htwL n hn
        rwa [smul_apply] at this
      have := dvd_of_smul_mem_addSubgroup h1 (hFcard n hn) (hv₀F n hn) htwFn
      rwa [Int.natCast_dvd_natCast] at this
    rw [hb0, mem_span_singleton]
    exact ⟨s, by rw [← hst, ht0, zero_smul, add_zero]⟩
  ·
    rw [hb0, span_singleton_le_iff_mem]
    exact hv₀L

end TateModule

theorem solution
    {M : Type} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (hcard : ∀ n, Nat.card (torsionBy ℤ M ((p^n : ℕ) : ℤ)) = (p^n)^2)
    (F : ℕ → AddSubgroup M) (P : M → Prop)
    (hFiff : ∀ m, 1 ≤ m → ∀ x, x ∈ F m ↔ ((p^m : ℕ) : ℤ) • x = 0 ∧ P x)
    (hFcard : ∀ m, 1 ≤ m → Nat.card (F m) = p^m)
    (L : Submodule ℤ_[p] (TateModule p M))
    (hL : ∀ x, x ∈ L ↔ ∀ m, 1 ≤ m → (x : ℕ → M) m ∈ F m) :
    ∃ b : Module.Basis (Fin 2) ℤ_[p] (TateModule p M), L = ℤ_[p] ∙ b 0 :=
  TateModule.exists_basis_span_eq_of_filtration_aux hcard F P hFiff hFcard L hL

end S_TateModule_exists_basis_span_eq_of_filtration
end P2MW
export P2MW.S_TateModule_exists_basis_span_eq_of_filtration (solution)
