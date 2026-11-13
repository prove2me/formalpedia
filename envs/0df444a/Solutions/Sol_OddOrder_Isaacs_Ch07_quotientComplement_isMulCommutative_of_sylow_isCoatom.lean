-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.quotientComplement_isMulCommutative_of_sylow_isCoatom
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:57:24.336208+00:00
-- url     : https://prove2.me/submissions/08150dab-bdbe-4efb-8e07-401db691c6b8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_AbelianQuotientComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped IsMulCommutative

section MinimalCounterexampleStepSix

/-- **Isaacs Theorem 7.1, Step 6 (abelian quotient complement).**

Assume that the Sylow `p`-subgroup `P` is maximal.  If `Nbar` is a normal
`p`-complement in `G/O_p(G)`, then `Nbar` is abelian.  Indeed, the inverse image
of `Pbar ⊔ W` for a `Pbar`-invariant subgroup `W ≤ Nbar` contains `P`; maximality
forces it to be either `P` or all of `G`.  Dedekind's law then gives
`W = ⊥` or `W = Nbar`.  An invariant Sylow subgroup shows that `Nbar` is a
prime-power group, and its invariant proper derived subgroup must be trivial. -/
theorem _root_.solution.{u}
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP_max : IsCoatom (P : Subgroup G))
    {Nbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)}
    (hNbar_normal : Nbar.Normal)
    (hNbar_complement : ∀ Pbar : Sylow p
      (G ⧸ OddOrder.Isaacs.Ch01.opCore p G),
      Subgroup.IsComplement' Nbar (Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) :
    IsMulCommutative ↥Nbar := by
  classical
  let : Nbar.Normal := hNbar_normal
  let q : G →* G ⧸ OddOrder.Isaacs.Ch01.opCore p G :=
    QuotientGroup.mk' (OddOrder.Isaacs.Ch01.opCore p G)
  have hq : Function.Surjective q :=
    QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.opCore p G)
  have hker : q.ker = OddOrder.Isaacs.Ch01.opCore p G := by
    dsimp [q]
    exact QuotientGroup.ker_mk' _
  set Pbar : Sylow p (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
    P.mapSurjective hq with hPbar_def
  have hPbar_coe :
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) =
        (P : Subgroup G).map q := by
    rw [hPbar_def, Sylow.coe_mapSurjective]
  have hPbar_comap :
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)).comap q =
        (P : Subgroup G) := by
    rw [hPbar_coe]
    exact Subgroup.comap_map_eq_self
      (by simpa only [hker] using OddOrder.Isaacs.Ch01.opCore_le P)
  have hcomp := hNbar_complement Pbar
  let phi : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) →*
      MulAut ↥Nbar :=
    (MulAut.conjNormal (H := Nbar)).comp
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)).subtype
  have hphi_val : ∀
      (a : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (n : ↥Nbar),
      (((phi a) n : ↥Nbar) : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) =
        (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
          (n : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
            (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G)⁻¹ := by
    intro a n
    simp only [phi, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulAut.conjNormal_apply]
  have hphi_inv_val : ∀
      (a : ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (n : ↥Nbar),
      (((phi a)⁻¹ n : ↥Nbar) : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) =
        (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G)⁻¹ *
          (n : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) *
            (a : G ⧸ OddOrder.Isaacs.Ch01.opCore p G) := by
    intro a n
    simp only [phi, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact MulAut.conjNormal_inv_apply (a :
      G ⧸ OddOrder.Isaacs.Ch01.opCore p G) n
  have invariant_dichotomy
      (W : Subgroup ↥Nbar)
      (hW_inv : OddOrder.Isaacs.Ch03.IsAInvariant phi W) :
      W = ⊥ ∨ W = ⊤ := by
    set Wbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
      W.map Nbar.subtype with hWbar_def
    have hWbar_le : Wbar ≤ Nbar := by
      rw [hWbar_def]
      exact Subgroup.map_subtype_le W
    have hPbar_normalizes_Wbar :
        (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) ≤
          Subgroup.normalizer (Wbar : Set
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · rintro ⟨n, hn, rfl⟩
        refine ⟨(phi ⟨a, ha⟩) n, hW_inv.smul_mem ⟨a, ha⟩ hn, ?_⟩
        exact hphi_val ⟨a, ha⟩ n
      · rintro ⟨n, hn, hn_eq⟩
        refine ⟨(phi ⟨a, ha⟩)⁻¹ n,
          hW_inv.inv_smul_mem ⟨a, ha⟩ hn, ?_⟩
        simp only [Subgroup.coe_subtype] at hn_eq ⊢
        rw [hphi_inv_val ⟨a, ha⟩ n, hn_eq]
        group
    set Hbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G) :=
      (Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) ⊔ Wbar
      with hHbar_def
    set H : Subgroup G := Hbar.comap q with hH_def
    have hP_le_H : (P : Subgroup G) ≤ H := by
      rw [hH_def, ← hPbar_comap]
      exact Subgroup.comap_mono (hHbar_def ▸ le_sup_left)
    have hH_map : H.map q = Hbar := by
      rw [hH_def]
      exact Subgroup.map_comap_eq_self_of_surjective hq Hbar
    rcases (hP_max.le_iff.mp hP_le_H) with hH_top | hH_P
    · have hHbar_top : Hbar = ⊤ := by
        calc
          Hbar = H.map q := hH_map.symm
          _ = (⊤ : Subgroup G).map q := by rw [hH_top]
          _ = ⊤ := Subgroup.map_top_of_surjective q hq
      have hmeet :
          (Wbar ⊔ (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) ⊓ Nbar = Wbar :=
        Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
          hWbar_le hcomp.disjoint.symm.eq_bot hPbar_normalizes_Wbar
      have hWbar_eq : Wbar = Nbar := by
        calc
          Wbar =
              (Wbar ⊔ (Pbar : Subgroup
                (G ⧸ OddOrder.Isaacs.Ch01.opCore p G))) ⊓ Nbar :=
            hmeet.symm
          _ = Hbar ⊓ Nbar := by rw [hHbar_def, sup_comm]
          _ = Nbar := by rw [hHbar_top, top_inf_eq]
      right
      apply Subgroup.map_injective Nbar.subtype_injective
      rw [← hWbar_def, hWbar_eq, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    · have hHbar_Pbar :
          Hbar = (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
        calc
          Hbar = H.map q := hH_map.symm
          _ = (P : Subgroup G).map q := by rw [hH_P]
          _ = (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := hPbar_coe.symm
      have hWbar_le_Pbar :
          Wbar ≤ (Pbar : Subgroup
            (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) := by
        rw [← hHbar_Pbar, hHbar_def]
        exact le_sup_right
      have hWbar_bot : Wbar = ⊥ := by
        rw [← le_bot_iff, ← hcomp.disjoint.symm.eq_bot]
        exact le_inf hWbar_le_Pbar hWbar_le
      left
      rw [hWbar_def] at hWbar_bot
      exact (Subgroup.map_eq_bot_iff_of_injective _
        Nbar.subtype_injective).mp hWbar_bot
  by_cases hNbar_bot : Nbar = ⊥
  · have : Subsingleton ↥Nbar := by
      rw [hNbar_bot]
      infer_instance
    infer_instance
  have : Nontrivial ↥Nbar :=
    Nbar.nontrivial_iff_ne_bot.mpr hNbar_bot
  obtain ⟨r, hr_prime, hr_dvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥Nbar)).ne'
  let : Fact r.Prime := ⟨hr_prime⟩
  have hp_not_dvd_Nbar : ¬ p ∣ Nat.card ↥Nbar := by
    intro hp_dvd
    apply Pbar.not_dvd_index
    simpa only [hcomp.index_eq_card] using hp_dvd
  have hcop : Nat.Coprime
      (Nat.card ↥(Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (Nat.card ↥Nbar) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Pbar.isPGroup'
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_Nbar)
  have : Group.IsNilpotent
      ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :=
    IsPGroup.isNilpotent Pbar.isPGroup'
  have : Group.IsSolvable
      ↥(Pbar : Subgroup (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)) :=
    inferInstance
  obtain ⟨R, hR_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow
      (A := ↥(Pbar : Subgroup
        (G ⧸ OddOrder.Isaacs.Ch01.opCore p G)))
      (G := ↥Nbar) (φ := phi) hcop (Or.inl inferInstance) r
  have hR_ne : (R : Subgroup ↥Nbar) ≠ ⊥ :=
    R.ne_bot_of_dvd_card hr_dvd
  have hR_top : (R : Subgroup ↥Nbar) = ⊤ := by
    rcases invariant_dichotomy (R : Subgroup ↥Nbar) hR_inv with hR_bot | hR_top
    · exact (hR_ne hR_bot).elim
    · exact hR_top
  have hNbar_r : IsPGroup r ↥Nbar := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp R.isPGroup'
    apply IsPGroup.of_card (n := k)
    calc
      Nat.card ↥Nbar = Nat.card ↥(⊤ : Subgroup ↥Nbar) := by simp
      _ = Nat.card ↥(R : Subgroup ↥Nbar) := by rw [hR_top]
      _ = r ^ k := hk
  have : Group.IsNilpotent ↥Nbar := IsPGroup.isNilpotent hNbar_r
  have : Group.IsSolvable ↥Nbar := inferInstance
  have hcomm_ne_top : commutator ↥Nbar ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Nbar).ne
  have hcomm_inv :
      OddOrder.Isaacs.Ch03.IsAInvariant phi (commutator ↥Nbar) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.commutator_self phi
  have hcomm_bot : commutator ↥Nbar = ⊥ := by
    rcases invariant_dichotomy (commutator ↥Nbar) hcomm_inv with hbot | htop
    · exact hbot
    · exact (hcomm_ne_top htop).elim
  exact (commutator_eq_bot_iff ↥Nbar).mp hcomm_bot

end MinimalCounterexampleStepSix

end OddOrder.Isaacs.Ch07
