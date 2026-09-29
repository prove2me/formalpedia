-- Prove2me | solution 1 for PDivisibleGroup.exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8b586f71-fdc3-5c30-8bf6-5d32f75abc3f

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

open Submodule
namespace TateModule
p2m_export "TateModule" "torsion compat compat_pow coe_zero natCast_smul_eq_of_zmod_eq toZModPow_eq_appr smul_apply natCast_padicInt_smul_apply proj proj_apply proj_mem_torsionBy shiftOfProjEqZero pow_smul_shiftOfProjEqZero smul_eq_zero_of_mem_torsionBy_one finite_torsionBy mulP kerMulPEquiv mulP_surjective liftFun liftFun_of_le coe_liftAux_congr liftFun_mem proj_surjective dvd_of_rel_apply levelMap levelMap_injective levelMap_bijective basisOfCard free"
namespace RankDBasis
p2m_open "TateModule"

variable {p : ℕ} {M : Type} [AddCommGroup M] [Fact p.Prime] {d : ℕ}

theorem finite_torsionBy
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Finite (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [hcard n]; exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

theorem mulP_surjective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    Function.Surjective (mulP p M n) := by
  haveI := finite_torsionBy hcard (n + 1)
  haveI := finite_torsionBy hcard n
  have hp : p.Prime := Fact.out
  have hker : Nat.card (mulP p M n).ker = p ^ d := by
    rw [Nat.card_congr (kerMulPEquiv p M n), hcard 1, pow_one]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (mulP p M n).ker
  rw [hcard (n + 1), Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulP p M n)).toEquiv,
    hker] at h
  have hrange : Nat.card (mulP p M n).range = Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) := by
    rw [hcard n]
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos d) ?_
    rw [← h, ← mul_pow, ← pow_succ]
  rw [← AddMonoidHom.range_eq_top]
  exact AddSubgroup.eq_top_of_card_eq _ hrange

theorem proj_surjective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) (n : ℕ) :
    ∀ m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ), ∃ x : TateModule p M, proj p M n x = m := by
  intro m hm
  choose next hnext using fun k (m : torsionBy ℤ M ((p ^ k : ℕ) : ℤ)) => mulP_surjective hcard k m
  refine ⟨⟨liftFun next n ⟨m, hm⟩,
    liftFun_mem (fun k m => congrArg Subtype.val (hnext k m)) n ⟨m, hm⟩⟩, ?_⟩
  rw [proj_apply]
  change liftFun next n ⟨m, hm⟩ n = m
  rw [liftFun_of_le le_rfl, coe_liftAux_congr (Nat.sub_self n)]
  rfl

theorem exists_family_of_card_eq_pow {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (hV : Nat.card V = p ^ d) :
    ∃ e : Fin d → V, ∀ a : Fin d → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  have hp : p.Prime := Fact.out
  have hrank : Module.finrank (ZMod p) V = d := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) V hrank
  refine ⟨b, fun a h i => ?_⟩
  have h' : ∑ j, (a j : ZMod p) • b j = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using h
  have hli := Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => (a j : ZMod p)) h' i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) p).mp hli

theorem exists_indep_family
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ e : Fin d → M, (∀ i, e i ∈ torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) ∧
      ∀ a : Fin d → ℤ, ∑ i, a i • e i = 0 → ∀ i, (p : ℤ) ∣ a i := by
  haveI := finite_torsionBy hcard 1
  have hmod : ∀ m : torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ), p • m = 0 := fun m =>
    Subtype.ext (by
      rw [coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℤ, Submodule.coe_zero]
      exact smul_eq_zero_of_mem_torsionBy_one m.2)
  letI : Module (ZMod p) (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) := AddCommGroup.zmodModule hmod
  have h1 : Nat.card (torsionBy ℤ M ((p ^ 1 : ℕ) : ℤ)) = p ^ d := by rw [hcard 1, pow_one]
  obtain ⟨e, he⟩ := exists_family_of_card_eq_pow (p := p) h1
  refine ⟨fun i => (e i : M), fun i => (e i).2, fun a ha => he a (Subtype.ext ?_)⟩
  rw [Submodule.coe_sum, Submodule.coe_zero, ← ha]
  exact Finset.sum_congr rfl fun i _ => coe_smul_of_tower _ _

omit [Fact p.Prime] in
theorem dvd_of_rel_apply {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ∀ (n : ℕ) (a : Fin d → ℤ), ∑ i, a i • (x i : ℕ → M) n = 0 →
      ∀ i, ((p ^ n : ℕ) : ℤ) ∣ a i := by
  intro n
  induction n with
  | zero => intro a _ i; simp
  | succ n ih =>
    intro a hab
    have hab1 : ∑ i, a i • (x i : ℕ → M) 1 = 0 := by
      have key : ∀ i, ((p ^ n : ℕ) : ℤ) • (a i • (x i : ℕ → M) (n + 1)) = a i • (x i : ℕ → M) 1 :=
        fun i => by
          rw [smul_comm, ← compat_pow (x i) 1 n, Nat.add_comm 1 n]
      have := congrArg (((p ^ n : ℕ) : ℤ) • ·) hab
      simp only [smul_zero, Finset.smul_sum, key] at this
      exact this
    have hdvd := h1 a hab1
    choose a' ha' using hdvd
    have hab' : ∑ i, a' i • (x i : ℕ → M) n = 0 := by
      have key : ∀ i, a i • (x i : ℕ → M) (n + 1) = a' i • (x i : ℕ → M) n := fun i => by
        rw [ha' i, mul_comm, mul_smul, compat]
      simpa only [key] using hab
    intro i
    rw [ha' i, pow_succ', Nat.cast_mul]
    exact mul_dvd_mul_left _ (ih a' hab' i)

noncomputable def levelMap (x : Fin d → TateModule p M) (n : ℕ) (c : Fin d → ZMod (p ^ n)) :
    torsionBy ℤ M ((p ^ n : ℕ) : ℤ) :=
  ⟨∑ i, ((c i).val : ℤ) • (x i : ℕ → M) n,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (proj_mem_torsionBy n (x i))⟩

theorem levelMap_injective {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Injective (levelMap x n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  intro c c' h
  have h' : ∑ i, (((c i).val : ℤ) - (c' i).val) • (x i : ℕ → M) n = 0 := by
    have := sub_eq_zero.mpr (congrArg Subtype.val h)
    simp only [levelMap] at this
    rw [← Finset.sum_sub_distrib] at this
    simpa only [sub_smul] using this
  have hdvd := dvd_of_rel_apply h1 n _ h'
  funext i
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub ((c' i).val : ℤ) ((c i).val : ℤ) (p ^ n)).mpr
    (hdvd i)
  rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    eq_comm] at this

theorem levelMap_bijective
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ) :
    Function.Bijective (levelMap x n) := by
  haveI := finite_torsionBy hcard n
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  refine (levelMap_injective h1 n).bijective_of_nat_card_le ?_
  rw [hcard n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_coeffs
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) (n : ℕ)
    {m : M} (hm : m ∈ torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    ∃ a : Fin d → ℕ, ∑ i, (a i : ℤ) • (x i : ℕ → M) n = m := by
  obtain ⟨c, hc⟩ := (levelMap_bijective hcard h1 n).2 ⟨m, hm⟩
  exact ⟨fun i => (c i).val, congrArg Subtype.val hc⟩

theorem exists_eq_sum_smul
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i)
    (z : TateModule p M) : ∃ s : Fin d → ℤ_[p], ∑ i, s i • x i = z := by
  choose a ha using fun n => exists_coeffs hcard h1 n (proj_mem_torsionBy n z)
  have hcompat : ∀ n i, ((p ^ n : ℕ) : ℤ) ∣ (a (n + 1) i : ℤ) - a n i := fun n =>
    dvd_of_rel_apply h1 n _ (by
      rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ ((x i : ℕ → M) n),
        Finset.sum_sub_distrib, ha n, sub_eq_zero, proj_apply, ← compat z n,
        ← proj_apply (n + 1) z, ← ha (n + 1), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, compat])
  have hca : ∀ i k, (p : ℤ) ^ k ∣ (fun k => (a k i : ℤ)) (k + 1) - (fun k => (a k i : ℤ)) k :=
    fun i k => by rw [← Nat.cast_pow]; exact hcompat k i
  refine ⟨fun i => PadicInt.ofIntSeq (fun k => (a k i : ℤ))
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (hca i)),
    Subtype.ext (funext fun n => ?_)⟩
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, ← proj_apply n z, ← ha n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply]
  refine natCast_smul_eq_of_zmod_eq (torsion (x i) n) ?_
  rw [← toZModPow_eq_appr,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a k i : ℤ)) p (hca i) n, Int.cast_natCast]

theorem exists_family
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    ∃ x : Fin d → TateModule p M,
      ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i := by
  obtain ⟨e, he, h1⟩ := exists_indep_family hcard
  choose x hx using fun i => proj_surjective hcard 1 (e i) (he i)
  refine ⟨x, ?_⟩
  have hx' : ∀ i, (x i : ℕ → M) 1 = e i := fun i => by rw [← proj_apply]; exact hx i
  simp_rw [hx']
  exact h1

theorem top_le_span
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d)
    {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    ⊤ ≤ span ℤ_[p] (Set.range x) := by
  rintro z -
  obtain ⟨s, hs⟩ := exists_eq_sum_smul hcard h1 z
  rw [← hs]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem coe_sum_smul_apply (s : Fin d → ℤ_[p]) (x : Fin d → TateModule p M) (n : ℕ) :
    ((∑ i, s i • x i : TateModule p M) : ℕ → M) n = ∑ i, (((s i).appr n : ℕ) : ℤ) • (x i : ℕ → M) n := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => smul_apply _ _ _

theorem linearIndependent_family {x : Fin d → TateModule p M}
    (h1 : ∀ a : Fin d → ℤ, ∑ i, a i • (x i : ℕ → M) 1 = 0 → ∀ i, (p : ℤ) ∣ a i) :
    LinearIndependent ℤ_[p] x := by
  refine Fintype.linearIndependent_iff.mpr fun s hs i => ?_
  have hlev : ∀ n, ((p ^ n : ℕ) : ℤ) ∣ (((s i).appr n : ℕ) : ℤ) := fun n =>
    dvd_of_rel_apply h1 n (fun j => (((s j).appr n : ℕ) : ℤ)) (by
      rw [← coe_sum_smul_apply, hs]; rfl) i
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [map_zero, toZModPow_eq_appr, ZMod.natCast_eq_zero_iff]
  exact Int.natCast_dvd_natCast.mp (hlev n)

noncomputable def basisOfCard
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Basis (Fin d) ℤ_[p] (TateModule p M) :=
  Module.Basis.mk (v := (exists_family hcard).choose)
    (linearIndependent_family (exists_family hcard).choose_spec)
    (top_le_span hcard (exists_family hcard).choose_spec)

theorem moduleFinite_and_free
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.Finite ℤ_[p] (TateModule p M) ∧ Module.Free ℤ_[p] (TateModule p M) :=
  ⟨Module.Finite.of_basis (basisOfCard hcard), Module.Free.of_basis (basisOfCard hcard)⟩

theorem finrank_eq
    (hcard : ∀ n : ℕ, Nat.card (torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ d) :
    Module.finrank ℤ_[p] (TateModule p M) = d := by
  rw [Module.finrank_eq_card_basis (basisOfCard hcard), Fintype.card_fin]

end TateModule.RankDBasis

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (L : Type) [CommRing L] [Algebra O L]
    (hcard : ∀ v : ℕ, Finite (H.Point L v) ∧ Nat.card (H.Point L v) = p ^ (v * h)) :
    (∀ (v : ℕ) (x : H.Point L v), ∃ y : TateModule p (H.Points L),
      (y : ℕ → H.Points L) v = H.pointsMkAdd L v (Additive.ofMul x)) ∧
    (∀ (v : ℕ) (y : TateModule p (H.Points L)),
      (y : ℕ → H.Points L) v = 0 ↔ ∃ z : TateModule p (H.Points L), y = ((p : ℤ_[p]) ^ v) • z) ∧
    Module.Free ℤ_[p] (TateModule p (H.Points L)) ∧ Module.finrank ℤ_[p] (TateModule p (H.Points L)) = h := by
  classical

  have htors : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ (H.Points L) ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ h := by
    intro n
    haveI := (hcard n).1
    let e : H.Point L n ≃ Submodule.torsionBy ℤ (H.Points L) ((p ^ n : ℕ) : ℤ) :=
      Equiv.ofBijective
        (fun x => ⟨H.pointsMkAdd L n (Additive.ofMul x), (Submodule.mem_torsionBy_iff _ _).2 (by
          change ((p ^ n : ℕ) : ℤ) • H.pointsMkAdd L n (Additive.ofMul x) = 0
          rw [natCast_zsmul]
          exact H.nsmul_pointsMkAdd_eq_zero n x)⟩)
        ⟨fun x y hxy => by
          have h' := congrArg Subtype.val hxy
          exact Additive.ofMul.injective (H.pointsMkAdd_injective n h'),
         fun z => by
          obtain ⟨z, hz⟩ := z
          obtain ⟨v, x, rfl⟩ := PDivisibleGroup.Points.exists_mkAdd H z
          have hz' : ((p ^ n : ℕ) : ℤ) • H.pointsMkAdd L v (Additive.ofMul x) = 0 :=
            (Submodule.mem_torsionBy_iff _ _).1 hz
          rcases le_total n v with hnv | hvn
          · have hx : x ^ (p ^ n) = 1 := by
              rw [natCast_zsmul, ← map_nsmul, ← ofMul_pow] at hz'
              exact Additive.ofMul.injective (H.pointsMkAdd_injective v (hz'.trans (map_zero _).symm))
            obtain ⟨x', rfl⟩ := H.exists_pointInclLE_eq_of_pow_eq_one hnv x hx
            exact ⟨x', Subtype.ext (H.pointsMkAdd_pointInclLE hnv x').symm⟩
          · exact ⟨H.pointInclLE L hvn x, Subtype.ext (H.pointsMkAdd_pointInclLE hvn x)⟩⟩
    rw [← Nat.card_congr e, (hcard n).2, ← pow_mul, mul_comm]
  refine ⟨fun v x => ?_, fun v y => ?_, (TateModule.RankDBasis.moduleFinite_and_free htors).2,
    TateModule.RankDBasis.finrank_eq htors⟩
  ·
    obtain ⟨y, hy⟩ := TateModule.RankDBasis.proj_surjective htors v (H.pointsMkAdd L v (Additive.ofMul x))
      ((Submodule.mem_torsionBy_iff _ _).2 (by
        change ((p ^ v : ℕ) : ℤ) • H.pointsMkAdd L v (Additive.ofMul x) = 0
        rw [natCast_zsmul]
        exact H.nsmul_pointsMkAdd_eq_zero v x))
    exact ⟨y, hy⟩
  ·
    constructor
    · intro hy
      exact ⟨TateModule.shiftOfProjEqZero v y hy, (TateModule.pow_smul_shiftOfProjEqZero v y hy).symm⟩
    · rintro ⟨z, rfl⟩
      rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply]
      exact TateModule.torsion z v

end S_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq
end P2MW
export P2MW.S_PDivisibleGroup_exists_tateModule_apply_eq_and_apply_eq_zero_iff_and_free_finrank_of_natCard_point_eq (solution)
