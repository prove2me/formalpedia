-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LengthMapIdealLe_proof_cd74b900e1b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:12:54.407005+00:00
-- url     : https://prove2.me/submissions/48f8b9f0-3401-40f2-8a43-6a300a8c41d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLengthMapIdealLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LengthMapIdealLe
theorem _root_.solution : LengthMapIdealLe.Statement.{u} := by
  intro C D _ _ _ φ hφ
  suffices key : ∀ n : ℕ, ∀ I : Ideal C, Module.length C (C ⧸ I) = n →
      Module.length D (D ⧸ I.map φ) ≤ n by
    intro I
    cases h : Module.length C (C ⧸ I) with
    | top => exact le_top
    | coe n => exact key n I h
  intro n
  induction n with
  | zero =>
    intro I hI
    have hs : Subsingleton (C ⧸ I) := Module.length_eq_zero_iff.mp (by exact_mod_cast hI)
    have hItop : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    subst hItop
    rw [Ideal.map_top]
    have : Subsingleton (D ⧸ (⊤ : Ideal D)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro I hI
    have hfin : IsFiniteLength C (C ⧸ I) :=
      Module.length_ne_top_iff.mp (by rw [hI]; exact ENat.natCast_ne_top _)
    have : IsArtinian C (C ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    have : Nontrivial (C ⧸ I) :=
      Module.length_pos_iff.mp (by rw [hI]; exact_mod_cast Nat.succ_pos n)
    have : IsAtomic (Submodule C (C ⧸ I)) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule C (C ⧸ I))).resolve_left top_ne_bot
    have hNs : IsSimpleModule C N := isSimpleModule_iff_isAtom.mpr hN

    have hlen : Module.length C (C ⧸ I) = Module.length C N + Module.length C ((C ⧸ I) ⧸ N) :=
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_one (R := C) (M := N), hI] at hlen
    have hq : Module.length C ((C ⧸ I) ⧸ N) = n := by
      have hx : Module.length C ((C ⧸ I) ⧸ N) ≠ ⊤ := by
        intro h
        rw [h, add_top] at hlen
        exact ENat.natCast_ne_top _ hlen
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hx
      rw [← hk] at hlen ⊢
      norm_cast at hlen ⊢
      omega

    obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN.1
    have hspan : Submodule.span C {v} = N :=
      (hN.le_iff.mp ((Submodule.span_singleton_le_iff_mem _ _).mpr hvN)).resolve_left
        (by simpa using hv0)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective v

    set I' : Ideal C := N.comap (Submodule.mkQ I) with hI'def
    have hII' : I ≤ I' := by
      intro x hx
      show Submodule.mkQ I x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).mpr hx]
      exact N.zero_mem
    have hI'N : Submodule.map (Submodule.mkQ I) I' = N :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective I) N
    have hlenI' : Module.length C (C ⧸ I') = n := by
      rw [← (Submodule.quotientQuotientEquivQuotient I I' hII').length_eq, hI'N, hq]
    have ih' := ih I' hlenI'

    set m : Ideal C := Module.annihilator C N
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmc : ∀ x ∈ m, x * c ∈ I := by
      intro x hx
      have h1 := Module.mem_annihilator.mp hx ⟨_, hvN⟩
      have h2 : x • (Ideal.Quotient.mk I c) = 0 := congrArg Subtype.val h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      simpa [Algebra.smul_def] using h2

    have hI'le : I' ≤ I ⊔ Ideal.span {c} := by
      intro x hx
      have hx' : Submodule.mkQ I x ∈ Submodule.span C {Ideal.Quotient.mk I c} := hspan ▸ hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx'
      have hxa : Ideal.Quotient.mk I x = Ideal.Quotient.mk I (a * c) := by
        rw [map_mul]
        simpa [Algebra.smul_def] using ha.symm
      have hd : x - a * c ∈ I := Ideal.Quotient.eq.mp hxa
      rw [show x = (x - a * c) + a * c by ring]
      exact Submodule.add_mem_sup hd (Ideal.mul_mem_left _ a (Ideal.subset_span rfl))

    set J : Ideal D := I.map φ
    set J' : Ideal D := I'.map φ
    have hJJ' : J ≤ J' := Ideal.map_mono hII'
    have hJ'le : J' ≤ J ⊔ Ideal.span {φ c} := by
      calc J' ≤ (I ⊔ Ideal.span {c}).map φ := Ideal.map_mono hI'le
        _ = J ⊔ Ideal.span {φ c} := by rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    set w : D ⧸ J := Submodule.Quotient.mk (p := J) (φ c)
    set K : Submodule D (D ⧸ J) := Submodule.map (Submodule.mkQ J) J'
    have hK : K ≤ Submodule.span D {w} := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, q, hq', rfl⟩ := Submodule.mem_sup.mp (hJ'le hy)
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq'
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero J).mpr hp,
        zero_add, ← smul_eq_mul, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self w)
    have hlenD : Module.length D (D ⧸ J) = Module.length D K + Module.length D (D ⧸ J') := by
      rw [Module.length_eq_add_of_exact K.subtype K.mkQ K.injective_subtype K.mkQ_surjective
        (LinearMap.exact_subtype_mkQ K), (Submodule.quotientQuotientEquivQuotient J J' hJJ').length_eq]

    have hmX : m.map φ ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, ← map_mul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_map_of_mem φ (hmc x hx)
    have hKle1 : Module.length D K ≤ 1 := by
      rcases hφ m hm with htop | hle
      · have hw : w = 0 := by
          have h1 : (1 : D) ∈ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
            hmX (htop ▸ Submodule.mem_top)
          simpa using h1
        have hK0 : K = ⊥ := le_bot_iff.mp (hK.trans (by simp [hw]))
        rw [hK0, Module.length_bot]
        exact zero_le
      · have h1 : maximalIdeal D ≤ LinearMap.ker (LinearMap.toSpanSingleton D (D ⧸ J) w) :=
          hle.trans hmX
        let f := (maximalIdeal D).liftQ (LinearMap.toSpanSingleton D (D ⧸ J) w) h1
        have hrange : LinearMap.range f = Submodule.span D {w} := by
          rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
        have : IsSimpleModule D (D ⧸ maximalIdeal D) :=
          isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
        calc Module.length D K ≤ Module.length D (Submodule.span D {w}) :=
              Module.length_le_of_injective (Submodule.inclusion hK) (Submodule.inclusion_injective hK)
          _ = Module.length D (LinearMap.range f) := by rw [hrange]
          _ ≤ Module.length D (D ⧸ maximalIdeal D) :=
              Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          _ = 1 := Module.length_eq_one _ _
    calc Module.length D (D ⧸ I.map φ) = Module.length D K + Module.length D (D ⧸ J') := hlenD
      _ ≤ 1 + n := add_le_add hKle1 ih'
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
end LengthMapIdealLe
end GroundTheory.Heights₂.Heights.NumbersDVR
