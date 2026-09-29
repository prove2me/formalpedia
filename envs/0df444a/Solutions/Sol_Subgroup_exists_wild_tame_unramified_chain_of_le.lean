-- Prove2me | solution 1 for Subgroup.exists_wild_tame_unramified_chain_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f5841b76-e7ba-5dde-9970-37849e5b07b6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_wild_tame_unramified_chain_of_le

set_option autoImplicit false
universe u
open Module
open scoped IntermediateField Pointwise

namespace Subgroup p2m_export "Subgroup" "Normal.comap one relIndex_subgroupOf closure mem_bot map_sup card_dvd_of_injective FiniteIndex finiteIndex_of_le inclusion zpowers relIndex ext relIndex_sup_left subtype_injective Normal subset_closure mem_zpowers mem_sup_right mem_map mem_comap comap_map_eq_self_of_injective inf_subgroupOf_right comap zpow_mem_zpowers finite_quotient_of_finiteIndex index relIndex_dvd_of_le_left map subgroupOf_map_subtype mem_subgroupOf mem_zpowers_iff mem_sup_left closure_le mk subgroupOf" end Subgroup
p2m_open_scoped "Subgroup" in

private theorem Subgroup.sup_subgroupOf_eq_aux {G : Type*} [Group G] {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    (H ⊔ K).subgroupOf L = H.subgroupOf L ⊔ K.subgroupOf L := by
  have h1 : (H.subgroupOf L ⊔ K.subgroupOf L).map L.subtype = H ⊔ K := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hH, inf_eq_left.mpr hK]
  rw [Subgroup.subgroupOf, ← h1, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L)]

set_option maxHeartbeats 1600000 in
theorem solution
    {G : Type*} [Group G] {q : ℕ} [Fact q.Prime]
    (U W : Subgroup G) [U.Normal] [U.FiniteIndex] [W.Normal] (hUW : U ≤ W)
    (hWq : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G) (hφt : (t ^ q)⁻¹ * (φ * t * φ⁻¹) ∈ W)
    (hgen : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W)
    (S H : Subgroup G) (hUH : U ≤ H) (hHS : H ≤ S) (hHn : (H.subgroupOf S).Normal) :
    ∃ P I : Subgroup G, H ≤ P ∧ P ≤ I ∧ I ≤ S ∧ (P.subgroupOf S).Normal ∧ (I.subgroupOf S).Normal ∧
      (∃ n : ℕ, (H.subgroupOf P).index = q ^ n) ∧ ¬ q ∣ (P.subgroupOf I).index ∧
      (∃ g ∈ S, ∀ s ∈ S, ∃ n : ℕ, (g ^ n)⁻¹ * s ∈ I) := by
  classical
  haveI hqp : Fact q.Prime := inferInstance

  haveI : W.FiniteIndex := Subgroup.finiteIndex_of_le hUW
  haveI : Finite (G ⧸ W) := Subgroup.finite_quotient_of_finiteIndex

  obtain ⟨tb, htb⟩ : ∃ tb : G ⧸ W, QuotientGroup.mk t = tb := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb : G ⧸ W, QuotientGroup.mk φ = fb := ⟨_, rfl⟩
  have hconj : fb * tb * fb⁻¹ = tb ^ q := by
    have h : (QuotientGroup.mk (t ^ q) : G ⧸ W) = QuotientGroup.mk (φ * t * φ⁻¹) := by
      rw [QuotientGroup.eq]; exact hφt
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, htb, hfb] at h
    exact h.symm

  have hordpos : 0 < orderOf tb := orderOf_pos tb
  have hcop : Nat.Coprime q (orderOf tb) := by
    have h1 : orderOf (tb ^ q) = orderOf tb := by
      rw [← hconj]
      have : fb * tb * fb⁻¹ = MulAut.conj fb tb := (MulAut.conj_apply fb tb).symm
      rw [this]
      exact orderOf_injective (MulAut.conj fb).toMonoidHom (MulAut.conj fb).injective tb
    rw [orderOf_pow' tb hqp.out.ne_zero] at h1
    have hg : Nat.gcd (orderOf tb) q = 1 := by
      rcases (Nat.div_eq_self).mp h1 with h | h
      · exact absurd h hordpos.ne'
      · exact h
    rw [Nat.coprime_comm]
    exact hg

  let Ib : Subgroup (G ⧸ W) := Subgroup.zpowers tb
  let I₀ : Subgroup G := Ib.comap (QuotientGroup.mk' W)
  have hI₀mem : ∀ g : G, g ∈ I₀ ↔ (QuotientGroup.mk g : G ⧸ W) ∈ Ib := fun _ => Iff.rfl
  have hWI₀ : W ≤ I₀ := by
    intro w hw
    rw [hI₀mem, (QuotientGroup.eq_one_iff w).mpr hw]
    exact one_mem _
  have htI₀ : t ∈ I₀ := by rw [hI₀mem, htb]; exact Subgroup.mem_zpowers tb
  have hsupI₀ : Subgroup.closure {t} ⊔ W = I₀ := by
    apply le_antisymm
    · rw [sup_le_iff, Subgroup.closure_le, Set.singleton_subset_iff]
      exact ⟨htI₀, hWI₀⟩
    · intro g hg
      rw [hI₀mem, Subgroup.mem_zpowers_iff] at hg
      obtain ⟨k, hk⟩ := hg
      have : (QuotientGroup.mk (t ^ k) : G ⧸ W) = QuotientGroup.mk g := by rw [QuotientGroup.mk_zpow, htb]; exact hk
      rw [QuotientGroup.eq] at this
      have hmem : t ^ k * ((t ^ k)⁻¹ * g) ∈ Subgroup.closure {t} ⊔ W :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_singleton t)) k))
          (Subgroup.mem_sup_right this)
      rwa [mul_inv_cancel_left] at hmem
  have hgen' : ∀ g : G, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I₀ := fun g => by rw [← hsupI₀]; exact hgen g

  have hconj_mem : ∀ x ∈ Ib, fb * x * fb⁻¹ ∈ Ib := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    have : fb * tb ^ k * fb⁻¹ = (fb * tb * fb⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [this, hconj, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers tb _
  have hconj_mem' : ∀ x ∈ Ib, fb⁻¹ * x * fb ∈ Ib := by

    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have htb : fb⁻¹ * tb * fb = tb ^ m := by
      have h1 : fb⁻¹ * (tb ^ q) * fb = tb := by
        rw [← hconj]; group
      calc fb⁻¹ * tb * fb = fb⁻¹ * ((tb ^ q) ^ m) * fb := by rw [hm]
        _ = (fb⁻¹ * (tb ^ q) * fb) ^ m := by
            rw [show fb⁻¹ * (tb ^ q) ^ m * fb = MulAut.conj fb⁻¹ ((tb ^ q) ^ m) by rw [MulAut.conj_apply, inv_inv],
              map_pow, MulAut.conj_apply, inv_inv]
        _ = tb ^ m := by rw [h1]
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    have : fb⁻¹ * tb ^ k * fb = (fb⁻¹ * tb * fb) ^ k := by
      rw [show fb⁻¹ * tb ^ k * fb = MulAut.conj fb⁻¹ (tb ^ k) by rw [MulAut.conj_apply, inv_inv], map_zpow,
        MulAut.conj_apply, inv_inv]
    rw [this, htb, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem_zpowers tb _
  have hconj_pow : ∀ (n : ℕ) (y : G ⧸ W), y ∈ Ib → fb ^ n * y * (fb ^ n)⁻¹ ∈ Ib := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      have h := hconj_mem _ (ih y hy)
      have heq : fb ^ (n + 1) * y * (fb ^ (n + 1))⁻¹ = fb * (fb ^ n * y * (fb ^ n)⁻¹) * fb⁻¹ := by
        rw [pow_succ']; group
      rw [heq]; exact h
  haveI hIbN : Ib.Normal := by
    refine ⟨fun y hy g => ?_⟩

    induction g using QuotientGroup.induction_on with
    | H g0 =>
      obtain ⟨n, hn⟩ := hgen' g0
      rw [hI₀mem] at hn
      obtain ⟨x, hxdef⟩ : ∃ x : G ⧸ W, QuotientGroup.mk ((φ ^ n)⁻¹ * g0) = x := ⟨_, rfl⟩
      rw [hxdef] at hn
      have hg0 : (QuotientGroup.mk g0 : G ⧸ W) = fb ^ n * x := by
        rw [← hxdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, hfb]; group
      have hxy : x * y * x⁻¹ = y := by

        rw [Subgroup.mem_zpowers_iff] at hn hy
        obtain ⟨a, ha⟩ := hn; obtain ⟨b, hb⟩ := hy
        rw [← ha, ← hb]; group
      rw [hg0, show fb ^ n * x * y * (fb ^ n * x)⁻¹ = fb ^ n * (x * y * x⁻¹) * (fb ^ n)⁻¹ by group, hxy]
      exact hconj_pow n y hy
  haveI hI₀N : I₀.Normal := Subgroup.Normal.comap hIbN _

  have hcardIb : Nat.card Ib = orderOf tb := Nat.card_zpowers tb
  have hrelWI₀ : W.relIndex I₀ = orderOf tb := by
    rw [← hcardIb]

    let f : I₀ →* (G ⧸ W) := (QuotientGroup.mk' W).comp I₀.subtype
    have hker : f.ker = W.subgroupOf I₀ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff (x : G)
    have hrange : f.range = Ib := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact (hI₀mem x).mp x.2
      · intro hy
        induction y using QuotientGroup.induction_on with
        | H g => exact ⟨⟨g, (hI₀mem g).mpr hy⟩, rfl⟩
    rw [Subgroup.relIndex, ← hker, ← hrange]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

  have hnormP : ((H ⊔ (W ⊓ S)).subgroupOf S).Normal := by
    rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]
    haveI := hHn
    haveI : (W.subgroupOf S).Normal := inferInstance
    infer_instance
  have hnormI : ((H ⊔ (I₀ ⊓ S)).subgroupOf S).Normal := by
    rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]
    haveI := hHn
    haveI : (I₀.subgroupOf S).Normal := inferInstance
    infer_instance

  have hreldvd : ∀ (L' L : Subgroup G), L' ≤ L → W.relIndex L' ∣ W.relIndex L := by
    intro L' L hle
    let f : (L' ⧸ W.subgroupOf L') →* (L ⧸ W.subgroupOf L) :=
      QuotientGroup.map _ _ (Subgroup.inclusion hle) (fun x hx => by
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]; exact hx)
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [MonoidHom.mem_ker] at hx
        change (QuotientGroup.mk (Subgroup.inclusion hle y) : L ⧸ W.subgroupOf L) = 1 at hx
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
        rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hx
    exact Subgroup.card_dvd_of_injective f hf
  refine ⟨H ⊔ (W ⊓ S), H ⊔ (I₀ ⊓ S), le_sup_left, sup_le_sup_left (inf_le_inf_right S hWI₀) H,
    sup_le hHS inf_le_right, hnormP, hnormI, ?_, ?_, ?_⟩
  ·
    haveI := hHn
    have h1 : (H.subgroupOf (H ⊔ (W ⊓ S))).index = (H.subgroupOf S).relIndex (W.subgroupOf S) := by
      rw [← Subgroup.relIndex, ← Subgroup.relIndex_subgroupOf (sup_le hHS inf_le_right : H ⊔ (W ⊓ S) ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right, Subgroup.relIndex_sup_left]
    have hUH' : U.subgroupOf S ≤ H.subgroupOf S := fun x hx => hUH hx
    have h2 : (H.subgroupOf S).relIndex (W.subgroupOf S) ∣ (U.subgroupOf S).relIndex (W.subgroupOf S) :=
      Subgroup.relIndex_dvd_of_le_left _ hUH'

    haveI : ((U.subgroupOf S).subgroupOf (W.subgroupOf S)).FiniteIndex := inferInstance
    haveI : Finite ((W.subgroupOf S) ⧸ (U.subgroupOf S).subgroupOf (W.subgroupOf S)) :=
      Subgroup.finite_quotient_of_finiteIndex
    have hPG : IsPGroup q ((W.subgroupOf S) ⧸ (U.subgroupOf S).subgroupOf (W.subgroupOf S)) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H w =>
        obtain ⟨a, ha⟩ := hWq ((w : S) : G) w.2
        refine ⟨a, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact ha
    obtain ⟨n, hn⟩ := hPG.exists_card_eq
    have h3 : (U.subgroupOf S).relIndex (W.subgroupOf S) = q ^ n := hn
    rw [h1]
    rw [h3] at h2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hqp.out).mp h2
    exact ⟨m, hm⟩
  ·
    haveI := hHn
    haveI : ((H ⊔ (W ⊓ S)).subgroupOf S).Normal := hnormP
    have hWS_le : W.subgroupOf S ≤ (H ⊔ (W ⊓ S)).subgroupOf S := by
      rw [Subgroup.sup_subgroupOf_eq_aux hHS inf_le_right, Subgroup.inf_subgroupOf_right]; exact le_sup_right
    have h1 : ((H ⊔ (W ⊓ S)).subgroupOf (H ⊔ (I₀ ⊓ S))).index
        = ((H ⊔ (W ⊓ S)).subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) := by
      rw [← Subgroup.relIndex, ← Subgroup.relIndex_subgroupOf (sup_le hHS inf_le_right : H ⊔ (I₀ ⊓ S) ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : I₀ ⊓ S ≤ S),
        Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : W ⊓ S ≤ S)]
      haveI : (H.subgroupOf S ⊔ (W ⊓ S).subgroupOf S).Normal := by
        rw [← Subgroup.sup_subgroupOf_eq_aux hHS (inf_le_right : W ⊓ S ≤ S)]; exact hnormP
      have : H.subgroupOf S ⊔ (I₀ ⊓ S).subgroupOf S
          = (H.subgroupOf S ⊔ (W ⊓ S).subgroupOf S) ⊔ (I₀ ⊓ S).subgroupOf S := by
        rw [sup_assoc]
        congr 1
        rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_right, eq_comm, sup_eq_right]
        exact fun x hx => hWI₀ hx
      rw [this, Subgroup.relIndex_sup_left]
    have h2 : ((H ⊔ (W ⊓ S)).subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S)
        ∣ (W.subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) := Subgroup.relIndex_dvd_of_le_left _ hWS_le
    have h3 : (W.subgroupOf S).relIndex ((I₀ ⊓ S).subgroupOf S) = W.relIndex (I₀ ⊓ S) :=
      Subgroup.relIndex_subgroupOf inf_le_right
    have h4 : W.relIndex (I₀ ⊓ S) ∣ W.relIndex I₀ := hreldvd _ _ inf_le_left
    rw [h1]
    intro hdvd
    have : q ∣ orderOf tb := by
      rw [← hrelWI₀]
      exact hdvd.trans (h2.trans (h3 ▸ h4))
    exact (Nat.Prime.coprime_iff_not_dvd hqp.out).mp hcop this
  ·
    haveI : Finite (G ⧸ I₀) := by
      haveI : I₀.FiniteIndex := Subgroup.finiteIndex_of_le hWI₀
      exact Subgroup.finite_quotient_of_finiteIndex
    let π : G →* G ⧸ I₀ := QuotientGroup.mk' I₀
    have hπ : ∀ g, π g = 1 ↔ g ∈ I₀ := fun g => QuotientGroup.eq_one_iff g
    haveI : IsCyclic (G ⧸ I₀) := by
      refine ⟨⟨π φ, fun x => ?_⟩⟩
      induction x using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨n, hn⟩ := hgen' g
        refine ⟨n, ?_⟩
        show (π φ) ^ (n : ℤ) = π g
        rw [zpow_natCast, ← map_pow]
        have : π ((φ ^ n)⁻¹ * g) = 1 := (hπ _).mpr hn
        rw [map_mul, map_inv, inv_mul_eq_one] at this
        exact this
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := S.map π)
    obtain ⟨g₀, hg₀S, hg₀⟩ := Subgroup.mem_map.mp γ.2
    refine ⟨g₀, hg₀S, fun s hs => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨π s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩⟩)
    have hk' : (π g₀) ^ k = π s := by
      have := congrArg Subtype.val hk
      simpa [hg₀] using this

    have hk'' : (π g₀) ^ (k % (orderOf (π g₀) : ℤ)).toNat = π s := by
      rw [← hk', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (orderOf_pos _).ne')),
        zpow_mod_orderOf]
    refine ⟨(k % (orderOf (π g₀) : ℤ)).toNat, ?_⟩
    have hmemI₀ : (g₀ ^ (k % (orderOf (π g₀) : ℤ)).toNat)⁻¹ * s ∈ I₀ := by
      rw [← hπ, map_mul, map_inv, map_pow, hk'', inv_mul_cancel]
    exact Subgroup.mem_sup_right ⟨hmemI₀, Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hg₀S _)) hs⟩

end S_Subgroup_exists_wild_tame_unramified_chain_of_le
end P2MW
export P2MW.S_Subgroup_exists_wild_tame_unramified_chain_of_le (solution)
