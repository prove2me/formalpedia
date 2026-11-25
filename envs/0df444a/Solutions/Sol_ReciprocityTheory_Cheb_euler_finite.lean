-- Prove2me | solution 1 for ReciprocityTheory.Cheb.euler_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:23.110549+00:00
-- url     : https://prove2.me/submissions/48ba6756-e651-4e60-9d4f-9c04e91ed4bb

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFac
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Theorems.Thm_ReciprocityTheory_Cheb_euler_fin_pow
import Theorems.Thm_ReciprocityTheory_Cheb_smooth_empty_iff
import Theorems.Thm_ReciprocityTheory_Cheb_smooth_insert_decomp
import Theorems.Thm_ReciprocityTheory_Cheb_smooth_insert_mul
import Theorems.Thm_ReciprocityTheory_Cheb_smooth_mul_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1)
    (S : Finset (Prm E)) :
    HasSum (Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1)) (∏ q ∈ S, (1 - f q.asIdeal)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have hT : (⊤ : Ideal (𝓞 E)) ≠ ⊥ := top_ne_bot
    have key : Set.indicator {a : NZIdeal E | Smooth ∅ a.1} (fun a => f a.1) =
        fun a => if a = ⟨⊤, hT⟩ then (1:ℂ) else 0 := by
      funext a
      by_cases h : a = ⟨⊤, hT⟩
      · subst h
        have hs : Smooth (∅ : Finset (Prm E)) (⊤ : Ideal (𝓞 E)) := (smooth_empty_iff hT).2 rfl
        rw [Set.indicator_of_mem (show (⟨⊤, hT⟩ : NZIdeal E) ∈ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_pos rfl]
        show f ⊤ = 1
        rw [← Ideal.one_eq_top, hf1]
      · have hs : ¬ Smooth (∅ : Finset (Prm E)) a.1 := by
          intro hs
          exact h (Subtype.ext ((smooth_empty_iff a.2).1 hs))
        rw [Set.indicator_of_notMem (show a ∉ {a : NZIdeal E | Smooth ∅ a.1} from hs), if_neg h]
    rw [key]
    exact hasSum_ite_eq _ _
  | insert q S hq ih =>
    rw [Finset.prod_insert hq]
    rw [← hasSum_subtype_iff_indicator] at ih ⊢
    have hgeo : HasSum (fun k : ℕ => f q.asIdeal ^ k) (1 - f q.asIdeal)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hlt q)
    have hs1 : Summable (fun k : ℕ => ‖f q.asIdeal ^ k‖) := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hlt q)
    have hs2 : Summable (fun b : {a : NZIdeal E | Smooth S a.1} => ‖f b.1.1‖) :=
      hsum.subtype _
    have hprod : HasSum (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1)
        ((1 - f q.asIdeal)⁻¹ * ∏ x ∈ S, (1 - f x.asIdeal)⁻¹) :=
      by
        have ih' : HasSum (fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) (∏ x ∈ S, (1 - f x.asIdeal)⁻¹) := ih
        have h3 : Summable (fun p : ℕ × {a : NZIdeal E | Smooth S a.1} => f q.asIdeal ^ p.1 * f p.2.1.1) :=
          summable_mul_of_summable_norm (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hs1 hs2
        exact HasSum.mul (f := fun k : ℕ => f q.asIdeal ^ k)
            (g := fun b : {a : NZIdeal E | Smooth S a.1} => f b.1.1) hgeo ih' h3
    have hne : ∀ (k : ℕ) (b : {a : NZIdeal E | Smooth S a.1}), q.asIdeal ^ k * b.1.1 ≠ ⊥ := by
      intro k b
      exact mul_ne_zero (pow_ne_zero _ q.ne_bot) b.1.2
    let e : ℕ × {a : NZIdeal E | Smooth S a.1} → {a : NZIdeal E | Smooth (insert q S) a.1} :=
      fun p => ⟨⟨q.asIdeal ^ p.1 * p.2.1.1, hne p.1 p.2⟩, smooth_insert_mul q p.1 p.2.2⟩
    have hbij : Function.Bijective e := by
      constructor
      · rintro ⟨k, b⟩ ⟨k', b'⟩ h
        have h' : q.asIdeal ^ k * b.1.1 = q.asIdeal ^ k' * b'.1.1 :=
          congrArg (fun x : {a : NZIdeal E | Smooth (insert q S) a.1} => x.1.1) h
        obtain ⟨h1, h2⟩ := smooth_mul_inj hq b.2 b'.2 h'
        subst h1
        have hb : b = b' := Subtype.ext (Subtype.ext h2)
        rw [hb]
      · rintro ⟨⟨a, ha⟩, hs⟩
        obtain ⟨k, b, hb, hbs, rfl⟩ := smooth_insert_decomp q ha hs
        exact ⟨(k, ⟨⟨b, hb⟩, hbs⟩), rfl⟩
    refine (Equiv.ofBijective e hbij).hasSum_iff.mp ?_
    convert hprod using 1
    funext p
    simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
    rw [hmul, euler_fin_pow f hf1 hmul]
end ReciprocityTheory.Cheb
