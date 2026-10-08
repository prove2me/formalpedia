-- Prove2me | solution 2 for SteinitzExchange.LocalSupermod.exc_iff_localization_matroidal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T19:15:29.495121+00:00
-- url     : https://prove2.me/submissions/6f4a3d03-08ac-4218-a71e-87c78b8c3128

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal
import Definitions.Def_SteinitzExchange_LocalSupermod_Localization
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction

set_option autoImplicit false

/- Complete checked body: ClosureSaturation -/
section

open Set
open SteinitzExchange.LocalSupermod

namespace SteinitzExchange.LocalSupermodProof

def pairingLinear {V : Type*} [Fintype V] (p : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun b := pairing p b
  map_add' x y := by
    simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ v, p v * (c * x v)) = c * ∑ v, p v * x v
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => by ring)

theorem pairing_lower_on_hull {V : Type*} [Fintype V]
    (A : Finset (V → ℤ)) (p : V → ℝ) (c : ℝ)
    (hc : ∀ x ∈ A, c ≤ pairing p (toReal x))
    {b : V → ℝ} (hb : b ∈ hull A) : c ≤ pairing p b := by
  have hsub : toReal '' (A : Set (V → ℤ)) ⊆ (pairingLinear p) ⁻¹' Ici c := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  exact convexHull_min hsub ((convex_Ici c).linear_preimage (pairingLinear p)) hb

theorem conj_le_at_member {V : Type*} [Fintype V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (p : V → ℝ)
    {x : V → ℤ} (hx : x ∈ B) :
    concaveConj B ω p ≤ pairing p (toReal x) - ω x := by
  have : Finite (B : Set (V → ℤ)) := B.finite_toSet.to_subtype
  exact ciInf_le (Set.finite_range
    (fun y : (B : Set (V → ℤ)) => pairing p (toReal y.val) - ω y.val)).bddBelow ⟨x, hx⟩

theorem pairing_sub_left {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p - q) b = pairing p b - pairing q b := by
  simp only [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem perturb_neg_eq {V : Type*} [Fintype V]
    (ω : (V → ℤ) → ℝ) (p : V → ℝ) (x : V → ℤ) :
    perturb ω (-p) x = ω x - pairing p (toReal x) := by
  simp only [perturb, pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem argmax_nonempty {V : Type*}
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    (argmaxB B g).Nonempty := by
  classical
  obtain ⟨a, ha, hmax⟩ := B.exists_max_image g hB
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, hmax⟩⟩

theorem hull_argmax_subset {V : Type*}
    (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) :
    hull (argmaxB B g) ⊆ hull B := by
  apply convexHull_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩

/-- Closure agreement supplies the integer saturation that the corrected localization
bridge needs. Only affine inequalities on the relevant hull are used. -/
theorem closure_agreement_argmax_saturated {V : Type*} [Fintype V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty)
    (hsat : ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B)
    (ω : (V → ℤ) → ℝ)
    (hclosure : ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x)
    (p₀ : V → ℝ) :
    ∀ z : V → ℤ, toReal z ∈ hull (argmaxB B (perturb ω (-p₀))) →
      z ∈ argmaxB B (perturb ω (-p₀)) := by
  classical
  let A := argmaxB B (perturb ω (-p₀))
  obtain ⟨a, ha⟩ := argmax_nonempty B hB (perturb ω (-p₀))
  have haB := (Finset.mem_filter.mp ha).1
  have haMax := (Finset.mem_filter.mp ha).2
  intro z hz
  have hzB : z ∈ B := hsat z (hull_argmax_subset B (perturb ω (-p₀)) hz)
  have hfamily (q : V → ℝ) :
      perturb ω (-p₀) a + pairing p₀ (toReal z) ≤
        pairing q (toReal z) - concaveConj B ω q := by
    have hvertices : ∀ x ∈ A,
        perturb ω (-p₀) a + concaveConj B ω q ≤ pairing (q - p₀) (toReal x) := by
      intro x hx
      have hxB := (Finset.mem_filter.mp hx).1
      have hxMax := (Finset.mem_filter.mp hx).2
      have he : perturb ω (-p₀) x = perturb ω (-p₀) a :=
        le_antisymm (haMax x hxB) (hxMax a haB)
      have hc := conj_le_at_member B ω q hxB
      rw [pairing_sub_left]
      simp only [perturb_neg_eq] at he ⊢
      linarith
    have h := pairing_lower_on_hull A (q - p₀)
      (perturb ω (-p₀) a + concaveConj B ω q) hvertices hz
    rw [pairing_sub_left] at h
    linarith
  have hlow : perturb ω (-p₀) a + pairing p₀ (toReal z) ≤
      concaveClosure B ω (toReal z) := le_ciInf hfamily
  rw [hclosure z hzB] at hlow
  refine Finset.mem_filter.mpr ⟨hzB, ?_⟩
  intro y hy
  have h := haMax y hy
  simp only [perturb_neg_eq] at h hlow ⊢
  linarith

end SteinitzExchange.LocalSupermodProof

end

/- Complete checked body: CheckedSteinitzSources -/
section

namespace AttributedSteinitz.Linear
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_add_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T10:21:39.246986+00:00
-- url     : https://prove2.me/submissions/65b90013-d8c6-4928-857a-3be72507b158


open SteinitzExchange.Extension

/-- The perturbation terms of a pair of points are unchanged by the exchange
`(x, y) ↦ (x − χ_u + χ_v, y + χ_u − χ_v)`, because the two exchanged points have
the same coordinate sum as the two original ones. -/
theorem pairing_add_cancel {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ)
    (x y : V → ℤ) (u v : V) :
    pairing p (toReal x) + pairing p (toReal y)
      = pairing p (toReal (x - chi u + chi v)) + pairing p (toReal (y + chi u - chi v)) := by
  have key : ∀ a b : V → ℤ,
      pairing p (toReal a) + pairing p (toReal b)
        = ∑ w, (p w * toReal a w + p w * toReal b w) := by
    intro a b
    simp only [pairing, Finset.sum_add_distrib]
  rw [key x y, key (x - chi u + chi v) (y + chi u - chi v)]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Pi.add_apply, Pi.sub_apply, toReal]
  push_cast
  ring

/-- Linearity lets one add a perturbation to an (EXC) inequality for free. -/
private theorem exc_ineq_perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ)
    (x y x' y' : V → ℤ)
    (hw : ω x + ω y ≤ ω x' + ω y')
    (hp : pairing p (toReal x) + pairing p (toReal y)
          = pairing p (toReal x') + pairing p (toReal y')) :
    perturb ω p x + perturb ω p y ≤ perturb ω p x' + perturb ω p y' := by
  calc perturb ω p x + perturb ω p y
      = (ω x + ω y) + (pairing p (toReal x) + pairing p (toReal y)) := by
        unfold perturb; ring
    _ ≤ (ω x' + ω y') + (pairing p (toReal x') + pairing p (toReal y')) :=
        add_le_add hw hp.le
    _ = perturb ω p x' + perturb ω p y' := by
        unfold perturb; ring

/-- Murota 1996, p. 280, Theorem 2.2 (under the standing assumption of §2.3 that `ω` satisfies
(EXC)): `ω[p]` satisfies (EXC) for every `p : V → ℝ`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (_hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, hx', hy', hineq⟩ := hω x hx y hy u hu
  exact ⟨v, hv, hx', hy',
    exc_ineq_perturb ω p x y (x - chi u + chi v) (y + chi u - chi v) hineq
      (pairing_add_cancel p x y u v)⟩

end AttributedSteinitz.Linear

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.exc_add_linear {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by
  exact AttributedSteinitz.Linear.solution B hB ω hω p
end


namespace AttributedSteinitz.Argmax
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.argmax_isIntegralBaseSet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:58:21.483525+00:00
-- url     : https://prove2.me/submissions/e9ab8555-facd-4c6b-aeac-d67679e98afa


namespace SteinitzExchange.Extension

theorem aux_amibs_mem_argmaxB {V : Type*} (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ)
    (x : V → ℤ) : x ∈ argmaxB B g ↔ x ∈ B ∧ ∀ y ∈ B, g y ≤ g x := by
  unfold argmaxB
  rw [Finset.mem_filter]

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    IsIntegralBaseSet (argmaxB B ω) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxB, hx⟩ := B.exists_max_image ω hB.1
    exact ⟨x, (aux_amibs_mem_argmaxB B ω x).2 ⟨hxB, hx⟩⟩
  · intro x hx y hy u hu
    rw [aux_amibs_mem_argmaxB] at hx hy
    obtain ⟨v, hv, hx', hy', hle⟩ := hω x hx.1 y hy.1 u hu
    refine ⟨v, hv, (aux_amibs_mem_argmaxB B ω _).2 ⟨hx', fun z hz => ?_⟩⟩
    have h1 := hy.2 _ hy'
    have h2 := hx.2 z hz
    linarith

end AttributedSteinitz.Argmax

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    IsIntegralBaseSet (argmaxB B ω) := by
  exact AttributedSteinitz.Argmax.solution B hB ω hω
end


namespace AttributedSteinitz.LocalExchange
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_iff_exc_loc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:21:52.882028+00:00
-- url     : https://prove2.me/submissions/1efc6787-f8e1-466d-8210-57e56423b465


namespace SteinitzExchange.Extension

lemma aux_eel_chi_apply {V : Type*} [DecidableEq V] (u w : V) :
    chi u w = if w = u then 1 else 0 := by
  simp [chi, Pi.single_apply]

lemma aux_eel_abs_sum {V : Type*} [Fintype V] [DecidableEq V] (i u j v : V) :
    ∑ w, (chi i w + chi u w + chi j w + chi v w) = 4 := by
  simp only [Finset.sum_add_distrib, chi, Finset.sum_pi_single', Finset.mem_univ, if_true]
  norm_num

lemma aux_eel_norm4 {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℤ) (i u j v : V)
    (hij : i ≠ j) (hiv : i ≠ v) (huj : u ≠ j) (huv : u ≠ v) :
    ∑ w, |(y + chi i - chi j + chi u - chi v) w - y w| = 4 := by
  have h : ∀ w, |(y + chi i - chi j + chi u - chi v) w - y w| =
      chi i w + chi u w + chi j w + chi v w := by
    intro w
    have e : (y + chi i - chi j + chi u - chi v) w - y w =
        (chi i w + chi u w) - (chi j w + chi v w) := by
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [e]
    have hi0 : 0 ≤ chi i w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hu0 : 0 ≤ chi u w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hj0 : 0 ≤ chi j w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hv0 : 0 ≤ chi v w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    by_cases hw : w = j ∨ w = v
    · have h1 : chi i w = 0 := by
        rw [aux_eel_chi_apply, if_neg]; rintro rfl; rcases hw with rfl | rfl <;> simp_all
      have h2 : chi u w = 0 := by
        rw [aux_eel_chi_apply, if_neg]; rintro rfl; rcases hw with rfl | rfl <;> simp_all
      rw [h1, h2, abs_of_nonpos (by linarith)]; ring
    · push Not at hw
      have h1 : chi j w = 0 := by rw [aux_eel_chi_apply, if_neg hw.1]
      have h2 : chi v w = 0 := by rw [aux_eel_chi_apply, if_neg hw.2]
      rw [h1, h2, abs_of_nonneg (by linarith)]; ring
  rw [Finset.sum_congr rfl (fun w _ => h w)]
  exact aux_eel_abs_sum i u j v

lemma aux_eel_abs1 (a : ℤ) (h : 0 < a) : |a - 1| ≤ |a| := by
  rw [abs_of_nonneg (by omega), abs_of_pos h]; omega

lemma aux_eel_abs2 (a : ℤ) (h : a < 0) : |a + 1| < |a| := by
  rw [abs_of_nonpos (by omega), abs_of_neg h]; omega

theorem aux_eel_main {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hloc : SatisfiesEXCLoc B ω) :
    ∀ n : ℕ, ∀ x ∈ B, ∀ y ∈ B, ∑ w, |x w - y w| < (n : ℤ) → ∀ u : V, 0 < (x - y) u →
    ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B ∧
      ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v) := by
  classical
  intro n
  induction n with
  | zero =>
    intro x _ y _ hn
    exact absurd hn (not_lt.mpr (by
      push_cast
      exact Finset.sum_nonneg (fun w _ => abs_nonneg _)))
  | succ n ih =>
    intro x hx y hy hn u hu
    by_contra H
    push Not at H
    -- the constant M
    have hMj : ∀ j, ω (y + chi u - chi j) - ω y <
        1 + ∑ j, |ω (y + chi u - chi j) - ω y| := by
      intro j
      have h1 := Finset.single_le_sum (f := fun j => |ω (y + chi u - chi j) - ω y|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 := le_abs_self (ω (y + chi u - chi j) - ω y)
      linarith
    let G : V → ℝ := fun j => if x - chi u + chi j ∈ B then ω x - ω (x - chi u + chi j)
      else 1 + ∑ j, |ω (y + chi u - chi j) - ω y|
    have hb : ∀ j, (x - y) j < 0 → y + chi u - chi j ∈ B →
        ω (y + chi u - chi j) - G j < ω y := by
      intro j hj hjB
      by_cases hxj : x - chi u + chi j ∈ B
      · have := H j hj hxj hjB
        simp only [G, if_pos hxj]; linarith
      · simp only [G, if_neg hxj]; linarith [hMj j]
    -- candidate set
    let P : V × V → Prop := fun p => 0 < (x - y) p.1 ∧ (p.1 = u → 2 ≤ (x - y) u) ∧
      (x - y) p.2 < 0 ∧ y + chi p.1 - chi p.2 ∈ B
    let C : Finset (V × V) := Finset.univ.filter P
    have hCne : C.Nonempty := by
      obtain ⟨v1, hv1, hx1⟩ := hB.2 x hx y hy u hu
      by_cases h2 : 2 ≤ (x - y) u
      · obtain ⟨i, hi, hiB⟩ := hB.2 y hy x hx v1 (by
          simp only [Pi.sub_apply] at hv1 ⊢; linarith)
        refine ⟨(i, v1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, hv1, ?_⟩⟩
        · simp only [Pi.sub_apply] at hi ⊢; linarith
        · intro _; exact h2
        · have e : y + chi i - chi v1 = y - chi v1 + chi i := by abel
          simp only [e]; exact hiB
      · have hu1 : (x - y) u = 1 := by omega
        by_cases hxy : x - chi u + chi v1 = y
        · exfalso
          have hyx : y + chi u - chi v1 = x := by rw [← hxy]; abel
          have := H v1 hv1 hx1 (by rw [hyx]; exact hx)
          rw [hxy, hyx] at this; linarith
        · have hw : ∃ w, 0 < (y - (x - chi u + chi v1)) w := by
            by_contra hw
            push Not at hw
            obtain ⟨a, ha⟩ : ∃ a, (x - chi u + chi v1) a ≠ y a := by
              by_contra hh; push Not at hh; exact hxy (funext hh)
            have ha' : 0 < ((x - chi u + chi v1) - y) a := by
              have := hw a; simp only [Pi.sub_apply] at this ⊢; omega
            obtain ⟨b, hb2, _⟩ := hB.2 _ hx1 y hy a ha'
            have := hw b; simp only [Pi.sub_apply] at this hb2; omega
          obtain ⟨w, hw⟩ := hw
          obtain ⟨a, ha, haB⟩ := hB.2 y hy _ hx1 w hw
          have huv1 : v1 ≠ u := by
            rintro rfl; simp only [Pi.sub_apply] at hu hv1; omega
          have hA1 : a ≠ u := by
            intro hau; rw [hau] at ha
            simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
              if_neg (Ne.symm huv1)] at ha
            simp only [Pi.sub_apply] at hu1; omega
          have hA2 : 0 < (x - y) a := by
            by_cases hav : a = v1
            · rw [hav] at ha
              simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
                if_neg huv1] at ha
              simp only [Pi.sub_apply] at hv1 ⊢; omega
            · simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hA1,
                if_neg hav] at ha
              simp only [Pi.sub_apply]; omega
          have hW : (x - y) w < 0 := by
            have hwu : w ≠ u := by
              intro hwu; rw [hwu] at hw
              simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
                if_neg (Ne.symm huv1)] at hw
              simp only [Pi.sub_apply] at hu1; omega
            by_cases hwv : w = v1
            · rw [hwv]; exact hv1
            · simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hwu,
                if_neg hwv] at hw
              simp only [Pi.sub_apply]; omega
          refine ⟨(a, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA2, ?_, hW, ?_⟩⟩
          · intro hau; exact absurd hau hA1
          · have e : y + chi a - chi w = y - chi w + chi a := by abel
            simp only [e]; exact haB
    obtain ⟨⟨i0, j0⟩, hp0, hmax⟩ :=
      Finset.exists_max_image C (fun p => ω (y + chi p.1 - chi p.2) - G p.2) hCne
    simp only [C, P, Finset.mem_filter, Finset.mem_univ, true_and] at hp0
    obtain ⟨hi0, hi0u, hj0, hy'B⟩ := hp0
    have hi0j0 : i0 ≠ j0 := by rintro rfl; omega
    have hu_j0 : u ≠ j0 := by rintro rfl; omega
    -- the new pair (x, y')
    have hmeas : ∑ w, |x w - (y + chi i0 - chi j0) w| < (n : ℤ) := by
      have hlt : ∑ w, |x w - (y + chi i0 - chi j0) w| < ∑ w, |x w - y w| := by
        apply Finset.sum_lt_sum
        · intro w _
          have e : x w - (y + chi i0 - chi j0) w = (x w - y w) - chi i0 w + chi j0 w := by
            simp only [Pi.add_apply, Pi.sub_apply]; ring
          rw [e]
          by_cases hw1 : w = i0
          · subst hw1
            rw [aux_eel_chi_apply, aux_eel_chi_apply, if_pos rfl, if_neg hi0j0]
            simp only [Pi.sub_apply] at hi0
            have := aux_eel_abs1 (x w - y w) hi0
            simpa using this
          · by_cases hw2 : w = j0
            · subst hw2
              rw [aux_eel_chi_apply, aux_eel_chi_apply, if_pos rfl, if_neg hw1]
              simp only [Pi.sub_apply] at hj0
              have := aux_eel_abs2 (x w - y w) hj0
              simp only [sub_zero]; exact this.le
            · rw [aux_eel_chi_apply, aux_eel_chi_apply, if_neg hw1, if_neg hw2]
              simp
        · refine ⟨j0, Finset.mem_univ _, ?_⟩
          have e : x j0 - (y + chi i0 - chi j0) j0 = (x j0 - y j0) + 1 := by
            simp only [Pi.add_apply, Pi.sub_apply, aux_eel_chi_apply, ↓reduceIte,
              if_neg (Ne.symm hi0j0)]; ring
          rw [e]
          simp only [Pi.sub_apply] at hj0
          exact aux_eel_abs2 _ hj0
      push_cast at hn
      omega
    have hux : 0 < (x - (y + chi i0 - chi j0)) u := by
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hu_j0]
      by_cases hiu : u = i0
      · rw [if_pos hiu]; have := hi0u hiu.symm; simp only [Pi.sub_apply] at this; omega
      · rw [if_neg hiu]; simp only [Pi.sub_apply] at hu; omega
    obtain ⟨v, hv, hxv, hzB, hineq⟩ := ih x hx _ hy'B hmeas u hux
    have hvW : (x - y) v < 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply] at hv ⊢
      by_cases hvi : v = i0
      · subst hvi; simp only [Pi.sub_apply] at hi0
        rw [if_pos rfl, if_neg hi0j0] at hv; omega
      · rw [if_neg hvi] at hv
        split_ifs at hv <;> omega
    have hi0v : i0 ≠ v := by rintro rfl; simp only [Pi.sub_apply] at hi0 hvW; omega
    have huv : u ≠ v := by rintro rfl; simp only [Pi.sub_apply] at hu hvW; omega
    have hdist := aux_eel_norm4 y i0 u j0 v hi0j0 hi0v hu_j0 huv
    obtain ⟨a, b, ha, hb', hzab, hyab, hloc'⟩ := hloc _ hzB y hy hdist
    have haa : a = i0 ∨ a = u := by
      by_contra hh
      push Not at hh
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hh.1, if_neg hh.2] at ha
      split_ifs at ha <;> omega
    have hbb : b = j0 ∨ b = v := by
      by_contra hh
      push Not at hh
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hh.1, if_neg hh.2] at hb'
      split_ifs at hb' <;> omega
    have hGv : G v = ω x - ω (x - chi u + chi v) := by simp only [G, if_pos hxv]
    have key : (ω (y + chi i0 - chi j0 + chi u - chi v) + ω y ≤
          ω (y + chi i0 - chi j0) + ω (y + chi u - chi v) ∧ y + chi u - chi v ∈ B) ∨
        (ω (y + chi i0 - chi j0 + chi u - chi v) + ω y ≤
          ω (y + chi i0 - chi v) + ω (y + chi u - chi j0) ∧ y + chi i0 - chi v ∈ B ∧
          y + chi u - chi j0 ∈ B) := by
      rcases haa with ha1 | ha1 <;> rcases hbb with hb1 | hb1 <;> rw [ha1, hb1] at hzab hyab hloc'
      · left
        have e : y + chi i0 - chi j0 + chi u - chi v - chi i0 + chi j0 = y + chi u - chi v := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hzab⟩
      · right
        have e : y + chi i0 - chi j0 + chi u - chi v - chi i0 + chi v = y + chi u - chi j0 := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hyab, hzab⟩
      · right
        have e : y + chi i0 - chi j0 + chi u - chi v - chi u + chi j0 = y + chi i0 - chi v := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hzab, hyab⟩
      · left
        have e : y + chi i0 - chi j0 + chi u - chi v - chi u + chi v = y + chi i0 - chi j0 := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hyab⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
    · have := hb v hvW k2
      linarith
    · have h1 := hb j0 hj0 k3
      have h2 := hmax (i0, v) (by
        simp only [C, P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi0, hi0u, hvW, k2⟩)
      simp only at h2
      linarith

theorem aux_eel_fwd {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (h : SatisfiesEXC B ω) :
    SatisfiesEXCLoc B ω := by
  intro x hx y hy hd
  have hne : x ≠ y := by
    rintro rfl; simp at hd
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ y a := by
    by_contra hh; push Not at hh; exact hne (funext hh)
  obtain ⟨u, hu⟩ : ∃ u, 0 < (x - y) u := by
    rcases lt_or_gt_of_ne ha with h1 | h1
    · obtain ⟨v, hv, _⟩ := h y hy x hx a (by simp only [Pi.sub_apply]; omega)
      exact ⟨v, by simp only [Pi.sub_apply] at hv ⊢; omega⟩
    · exact ⟨a, by simp only [Pi.sub_apply]; omega⟩
  obtain ⟨v, hv, h1, h2, h3⟩ := h x hx y hy u hu
  exact ⟨u, v, hu, hv, h1, h2, h3⟩

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ SatisfiesEXCLoc B ω := by
  constructor
  · exact aux_eel_fwd B ω
  · intro hloc x hx y hy u hu
    exact aux_eel_main B hB ω hloc ((∑ w, |x w - y w|).toNat + 1) x hx y hy
      (by push_cast; omega) u hu

end AttributedSteinitz.LocalExchange

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.exc_iff_exc_loc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ SatisfiesEXCLoc B ω := by
  exact AttributedSteinitz.LocalExchange.solution B hB ω
end


namespace AttributedSteinitz.SupportingFace
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.exists_perturb_hull_argmax
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T17:38:55.350079+00:00
-- url     : https://prove2.me/submissions/f3a900c7-d281-42e0-98c9-71f9b8ee4a86


/- BUNDLE COMPONENT: FarkasPort -/

/-
Ported from https://github.com/jmoy/farkas_lean
Copyright 2026 Jyotirmoy Bhattacharya

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

universe u v
set_option autoImplicit false

/- Original module: AlgebraHelpers -/

open Matrix

namespace FarkasLemma

lemma mulVec_lastCases_split
    {m : Type*} {F : Type*} [Semiring F] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F)
    (xₙ : F)
    (x' : Fin n → F)
    (i : m) :
    A.mulVec (Fin.lastCases xₙ x') i
      = (A.submatrix id Fin.castSucc i ⬝ᵥ x') + A i (Fin.last n) * xₙ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma dotProduct_mul_right
  {F : Type*} [CommSemiring F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c) ⬝ᵥ x) = (a ⬝ᵥ x) * c := by
  calc
    ((fun j : Fin n => a j * c) ⬝ᵥ x)
        = ∑ j : Fin n, (a j * c) * x j := by simp [dotProduct]
    _ = ∑ j : Fin n, (a j * x j) * c := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Fin n, a j * x j) * c := by
          rw [← Finset.sum_mul]
    _ = (a ⬝ᵥ x) * c := by simp [dotProduct]

lemma dotProduct_scaled_inv_mul
    {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F)
    (hc : c ≠ 0) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c = a ⬝ᵥ x := by
  calc
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c
        = ((a ⬝ᵥ x) * c⁻¹) * c := by
            rw [dotProduct_mul_right]
    _ = a ⬝ᵥ x := by
          field_simp [hc]

lemma dotProduct_mul_inv
  {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) = (a ⬝ᵥ x) * c⁻¹ := by
  simpa using dotProduct_mul_right a x c⁻¹

lemma split_add_mul_inv
    {F : Type*} [Field F]
    (u x c : F)
    (hc : c ≠ 0) :
    ((u + c * x) * c⁻¹) = u * c⁻¹ + x := by
  calc
    ((u + c * x) * c⁻¹)
        = u * c⁻¹ + (c * x) * c⁻¹ := by ring
    _ = u * c⁻¹ + x := by
          have hx : (c * x) * c⁻¹ = x := by
            calc
              (c * x) * c⁻¹ = x * (c * c⁻¹) := by ring
              _ = x := by simp [mul_inv_cancel₀ hc]
          simp [hx]

lemma mul_inv_cancel_right
    {F : Type*} [Field F]
    (a c : F)
    (hc : c ≠ 0) :
    (a * c⁻¹) * c = a := by
  calc
    (a * c⁻¹) * c = a * (c⁻¹ * c) := by ring
    _ = a := by simp [inv_mul_cancel₀ hc]

lemma upper_bound_from_linear_pos
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : 0 < c)
    (hlin : u + c * x ≤ b) :
    x + u * c⁻¹ ≤ b * c⁻¹ := by
  have hscaled : (u + c * x) * c⁻¹ ≤ b * c⁻¹ :=
    mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr (le_of_lt hc))
  calc
    x + u * c⁻¹ = u * c⁻¹ + x := by ring
    _ = (u + c * x) * c⁻¹ := by
          symm
          exact split_add_mul_inv u x c (ne_of_gt hc)
    _ ≤ b * c⁻¹ := hscaled

lemma lower_bound_from_linear_neg
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : c < 0)
    (hlin : u + c * x ≤ b) :
    b * c⁻¹ ≤ x + u * c⁻¹ := by
  have hscaled : b * c⁻¹ ≤ (u + c * x) * c⁻¹ :=
    mul_le_mul_of_nonpos_right hlin (inv_nonpos.mpr (le_of_lt hc))
  calc
    b * c⁻¹ ≤ (u + c * x) * c⁻¹ := hscaled
    _ = u * c⁻¹ + x := split_add_mul_inv u x c (ne_of_lt hc)
    _ = x + u * c⁻¹ := by ring

end FarkasLemma

/- Original module: FourierMotzkin -/

namespace FarkasLemma

-- A helper lemma first

-- Given finite index sets of lower and upper bounds in a lattice, if every lower bound
-- is below every upper bound, then there exists an element lying between all lowers
-- and all uppers.
--
-- If one side is empty, the witness is chosen from the nonempty side via `sup'`/`inf'`;
-- if both are empty, a witness is provided by `h_nonempty`.
private lemma finite_bounds_witness
    {ι : Type*} [Finite ι]
    {κ : Type*} [Finite κ]
    {F : Type*} [Lattice F]
    (h_nonempty : Nonempty F)
    (lhss : ι → F)
    (rhss : κ → F)
    (h : ∀ i j, lhss i ≤ rhss j) :
    ∃ x : F, ((∀ i, lhss i ≤ x) ∧ (∀ j, x ≤ rhss j)) := by
  have:= Fintype.ofFinite ι
  have:= Fintype.ofFinite κ
  by_cases hi: Nonempty ι
  · -- lhss is nonempty, use sup over it
    exact ⟨ Finset.univ.sup' Finset.univ_nonempty lhss,
            fun i => Finset.univ.le_sup' lhss (Finset.mem_univ i),
            fun j => Finset.sup'_le _ _ (fun i _ => h i j) ⟩
  · by_cases hj: Nonempty κ
    · -- rhss is nonempty, use inf over it
      exact ⟨ Finset.univ.inf' Finset.univ_nonempty rhss,
              fun i => False.elim (hi ⟨i⟩),
              fun j => Finset.univ.inf'_le _ (Finset.mem_univ j) ⟩
    · -- both are empty, any element will do
      obtain ⟨x⟩ := h_nonempty
      exact ⟨x,fun i => False.elim (hi ⟨i⟩),
               fun j => False.elim (hj ⟨j⟩)⟩

/--
`Fourier_Motzkin` performs one-step Fourier–Motzkin elimination on the last variable
of a finite linear system `A.mulVec x ≤ b`.

It constructs a finite index type `κ` and a nonnegative matrix `M` such that:
* the last column is eliminated: `(M * A) i (Fin.last n) = 0`,
* feasibility is preserved and reflected:
  the original system in `n+1` variables is feasible iff the projected system
  `(M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b` is feasible in `n` variables.

This is the standard elimination step used in proofs of Farkas-type results.
-/
theorem Fourier_Motzkin
  {m : Type u}
  {F : Type v}
  [Fintype m]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {n : ℕ}
  (A : Matrix m (Fin (n + 1)) F)
  (b : m → F) :
  ∃ κ : Type u, ∃ _ : Fintype κ, ∃ M : Matrix κ m F,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      ((∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b) := by
  /-

  ----------------------------------------------
  PART 1. Definitions and setup.
  ----------------------------------------------

  -/
  -- For notational convenience split A into last column and other columns
  let Aₙ : m → F := fun i => A i (Fin.last n)
  let A₀ : Matrix m (Fin n) F := A.submatrix id Fin.castSucc
  -- Partition rows by the sign of the eliminated variable coefficient.
  let posRow : Finset m := Finset.univ.filter (fun i => 0 < Aₙ i)
  let negRow : Finset m := Finset.univ.filter (fun i => Aₙ i < 0)
  let zeroRow : Finset m := Finset.univ.filter (fun i => Aₙ i = 0)
  -- New row index type after elimination:
  -- * `inl (iPos, iNeg)` for combined inequalities from positive/negative rows,
  -- * `inr iZero` for rows already independent of the eliminated variable.
  let κ : Type _ := ((↥posRow × ↥negRow) ⊕ ↥zeroRow)
  -- Normalized coefficient/bound functions used to isolate `xₙ`.
  let posCoeffs : posRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let posb : posRow -> F := fun i => b i * (Aₙ i)⁻¹
  let negCoeffs : negRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let negb : negRow -> F := fun i => b i * (Aₙ i)⁻¹
  let zeroCoeffs : zeroRow -> Fin n -> F := fun i j => A₀ i j
  let zerob : zeroRow -> F := fun i => b i
  -- Eliminated system `(A', b')` in `n` variables.
  let A' : Matrix κ (Fin n) F := fun i j => match i with
    | Sum.inl (iPos, iNeg) => posCoeffs iPos j - negCoeffs iNeg j
    | Sum.inr iZero => zeroCoeffs iZero j
  let b' : κ -> F := fun i => match i with
    | Sum.inl (iPos, iNeg) => posb iPos - negb iNeg
    | Sum.inr iZero => zerob iZero
  /-

  ----------------------------------------------
  PART 2. Forward direction.
  ----------------------------------------------
  Every solution of the original system projects to
  a solution of the eliminated system.


  -/
  have hlft: ∀ x : Fin (n + 1) → F,
        A.mulVec x ≤ b → ∃ x' : Fin n → F, A'.mulVec x' ≤ b' := by
    intro x hx
    -- Just dropping the last coordinate is going to be enough
    -- But the value of the last coordinate will have work to do.
    let x' : Fin n → F := fun j => x (Fin.castSucc j)
    let xₙ := x (Fin.last n)
    use x'
    intro i
    match i with
    | Sum.inl (iPos, iNeg) =>
      -- We have to satisfy a combined inequality arising from a positive
      -- and a negative row.
      -- Strategy: use the eliminated coordinate `xₙ` itself as a witness.
      -- From the positive row we derive an upper bound on `xₙ`, and from the
      -- negative row a lower bound on `xₙ`; combining these yields the reduced
      -- inequality for the `(iPos, iNeg)` row.
      --
      -- Now the real work begins. We will use xₙ to chain two inequalities
      -- Derive the upper-bound inequality for xₙ from the positive row.
      have h₁ : xₙ ≤ posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        have hpos : 0 < Aₙ iPos := (Finset.mem_filter.mp iPos.property).2
        have hrow_pos := hx iPos
        have hpos_ne : Aₙ iPos ≠ 0 := ne_of_gt hpos
        have hlin_pos :
            (A₀ iPos ⬝ᵥ x') + Aₙ iPos * xₙ ≤ b iPos := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_pos
        have hdot_pos :
            (posCoeffs iPos) ⬝ᵥ x' = (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by
          simpa [posCoeffs] using dotProduct_mul_inv (A₀ iPos) x' (Aₙ iPos)
        have hbound_pos : xₙ + (posCoeffs iPos) ⬝ᵥ x' ≤ posb iPos := by
          calc
            xₙ + (posCoeffs iPos) ⬝ᵥ x'
                = xₙ + (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by rw [hdot_pos]
            _ ≤ b iPos * (Aₙ iPos)⁻¹ :=
              upper_bound_from_linear_pos
                (A₀ iPos ⬝ᵥ x') xₙ (b iPos) (Aₙ iPos) hpos hlin_pos
            _ = posb iPos := by simp [posb]
        simpa [le_sub_iff_add_le] using hbound_pos
      -- Derive the lower-bound inequality for xₙ from the negative row.
      have h₂ : negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤ xₙ := by
        have hneg : Aₙ iNeg < 0 := (Finset.mem_filter.mp iNeg.property).2
        have hrow_neg := hx iNeg
        have hneg_ne : Aₙ iNeg ≠ 0 := ne_of_lt hneg
        have hlin_neg :
            (A₀ iNeg ⬝ᵥ x') + Aₙ iNeg * xₙ ≤ b iNeg := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_neg
        have hdot_neg :
            (negCoeffs iNeg) ⬝ᵥ x' = (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ := by
          simpa [negCoeffs] using dotProduct_mul_inv (A₀ iNeg) x' (Aₙ iNeg)
        have hbound_neg : negb iNeg ≤ xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by
          calc
            negb iNeg = b iNeg * (Aₙ iNeg)⁻¹ := by simp [negb]
            _ ≤ xₙ + (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ :=
              lower_bound_from_linear_neg
                (A₀ iNeg ⬝ᵥ x') xₙ (b iNeg) (Aₙ iNeg) hneg hlin_neg
            _ = xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by rw [hdot_neg]
        simpa [sub_le_iff_le_add] using hbound_neg
      -- Combine the upper and lower bounds to get the eliminated inequality.
      have h_combined : (posCoeffs iPos) ⬝ᵥ x' - negCoeffs iNeg ⬝ᵥ x'
                          ≤ posb iPos - negb iNeg := by
        linarith [h₁, h₂]
      simpa [A', b', Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using h_combined
    --
    | Sum.inr iZero =>
      -- A zero row is easy, the reduced inequality is the same as the original
      simp only [A', b', Matrix.mulVec,zeroCoeffs, zerob]
      have hzero : Aₙ iZero = 0 := (Finset.mem_filter.mp iZero.property).2
      have hzero' : A iZero (Fin.last n) = 0 := by simpa [Aₙ] using hzero
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hzero', A₀, x'] using hx iZero
  /-

  ----------------------------------------------
  PART 3. Backward direction.
  ----------------------------------------------

  From an eliminated solution, reconstruct a witness
  for the eliminated coordinate and then lift back to the original system.



  -/
  have hright : ∀ x' : Fin n → F,
        A'.mulVec x' ≤ b' → ∃ x : Fin (n + 1) → F, A.mulVec x ≤ b := by
    intro x' hsol
    -- Candidate lower/upper bounds for the eliminated variable.
    let valpos : posRow → F := fun i => posb i - (posCoeffs i) ⬝ᵥ x'
    let valneg : negRow → F := fun i => negb i - (negCoeffs i) ⬝ᵥ x'
    -- Pairwise compatibility of lower and upper bounds follows from `hsol`.
    have hbounds : ∀ iNeg iPos, valneg iNeg ≤ valpos iPos := by
      intro iNeg iPos
      have := hsol (Sum.inl (iPos, iNeg))
      dsimp [A', b'] at this
      have hlin :
          (posCoeffs iPos) ⬝ᵥ x' - (negCoeffs iNeg) ⬝ᵥ x' ≤ posb iPos - negb iNeg := by
        simpa [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using this
      have hbound :
          negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤
        posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        linarith [hlin]
      simpa [valpos, valneg] using hbound
    -- Choose `xₙ` between all lower and upper bounds.
    obtain ⟨xₙ, h_xₙn, h_xₙp⟩ := finite_bounds_witness ⟨0⟩ valneg valpos hbounds
    -- Reassemble the full vector from `xₙ` and `x'`.
    let x : Fin (n + 1) → F := Fin.lastCases xₙ x'
    -- We need to show that this will work
    refine ⟨x, fun i => ?_⟩
    by_cases hlast : Aₙ i = 0
    -- The zero row is the easy case
    · let iZero : zeroRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlast⟩⟩
      have hlast' : A i (Fin.last n) = 0 := by simpa [Aₙ] using hlast
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hlast', x, A', b', zeroCoeffs, zerob,
        A₀, iZero]
        using hsol (Sum.inr iZero)
    · cases lt_or_gt_of_ne hlast with
      | inl hneg =>
      -- Negative row
        let iNeg : negRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hneg⟩⟩
        have hiNeg : (iNeg : m) = i := rfl
        have h := h_xₙn iNeg
        dsimp [valneg] at h
        rw [sub_le_iff_le_add] at h
        rw [add_comm] at h
        have h_scaled := mul_le_mul_of_nonpos_right h (le_of_lt hneg)
        have h_scaled' : (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg ≤ negb iNeg * Aₙ iNeg := by
          simpa [hiNeg, add_comm] using h_scaled
        have hdot_neg : A₀ i ⬝ᵥ x' = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iNeg ⬝ᵥ x' := by simp [hiNeg]
            _ = ((fun j : Fin n => A₀ iNeg j * (Aₙ iNeg)⁻¹) ⬝ᵥ x') * Aₙ iNeg := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iNeg) x' (Aₙ iNeg) (ne_of_lt hneg)
            _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg + xₙ * Aₙ iNeg := by
                rw [hdot_neg]
                simp [Aₙ, hiNeg, mul_comm]
          _ = (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by ring
          _ ≤ negb iNeg * Aₙ iNeg := h_scaled'
          _ = b i := by
                calc
                  negb iNeg * Aₙ iNeg
                      = (b iNeg * (Aₙ iNeg)⁻¹) * Aₙ iNeg := by simp [negb]
                  _ = b iNeg := by
                    simpa using mul_inv_cancel_right (b iNeg) (Aₙ iNeg) (ne_of_lt hneg)
                  _ = b i := by simp [hiNeg]
      | inr hpos =>
      -- Positive row
        let iPos : posRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩⟩
        have hiPos : (iPos : m) = i := rfl
        have h := h_xₙp iPos
        dsimp [valpos] at h
        rw [le_sub_iff_add_le, add_comm] at h
        have h_scaled := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        have h_scaled' : ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos ≤ posb iPos * Aₙ iPos := by
          simpa [hiPos] using h_scaled
        have hdot_pos : A₀ i ⬝ᵥ x' = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iPos ⬝ᵥ x' := by simp [hiPos]
            _ = ((fun j : Fin n => A₀ iPos j * (Aₙ iPos)⁻¹) ⬝ᵥ x') * Aₙ iPos := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iPos) x' (Aₙ iPos) hpos.ne'
            _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos + xₙ * Aₙ iPos := by
                rw [hdot_pos]
                simp [Aₙ, hiPos, mul_comm]
          _ = ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos := by ring
          _ ≤ posb iPos * Aₙ iPos := h_scaled'
          _ = b i := by
                calc
                  posb iPos * Aₙ iPos
                      = (b iPos * (Aₙ iPos)⁻¹) * Aₙ iPos := by simp [posb]
                  _ = b iPos := by
                    simpa using mul_inv_cancel_right (b iPos) (Aₙ iPos) hpos.ne'
                  _ = b i := by simp [hiPos]
  /-

  ----------------------------------------------
  PART 4. Assembling the products
  ----------------------------------------------

  The difficult mathematical work has been done.
  Now we have to assemble the products into the form required by
  the statement of the theorem.

  -/
  classical
  -- Build a nonnegative combination matrix `M` realizing the elimination:
  -- rows for `(iPos,iNeg)` combine one positive and one negative row,
  -- zero rows are copied.
  let M : Matrix κ m F := fun i j =>
    match i with
    | Sum.inl (iPos, iNeg) =>
      (if (j : m) = (iPos : m) then (Aₙ iPos)⁻¹ else 0) +
      (if (j : m) = (iNeg : m) then -(Aₙ iNeg)⁻¹ else 0)
    | Sum.inr iZero =>
        if (j : m) = (iZero : m) then 1 else 0
  -- Identify abstract eliminated data `(A', b')` with matrix expressions via `M`.
  have hA'_eq : A' = M * A₀ := by
    ext i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mul_apply]
      simp [A', M, posCoeffs, negCoeffs, A₀, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [A', M, zeroCoeffs, A₀]
  have hb'_eq : b' = M.mulVec b := by
    ext i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, posb, negb, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, zerob]
  -- `M` is entrywise nonnegative.
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      refine add_nonneg ?_ ?_
      · by_cases h : (j : m) = (iPos : m)
        · simpa [M, h] using inv_nonneg.mpr (le_of_lt (Finset.mem_filter.mp iPos.property).2)
        · simp [h]
      · by_cases h : (j : m) = (iNeg : m)
        · simpa [M, h]
            using neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt (Finset.mem_filter.mp iNeg.property).2))
        · simp [h]
    | inr iZero =>
      by_cases h0 : (j : m) = (iZero : m)
      · simp [M, h0]
      · simp [M, h0]
  -- Multiplying by `M` eliminates the last column exactly.
  have hM_last_zero : ∀ i, (M * A) i (Fin.last n) = 0 := by
    intro i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      have hposnz : Aₙ iPos ≠ 0 := ne_of_gt (Finset.mem_filter.mp iPos.property).2
      have hnegnz : Aₙ iNeg ≠ 0 := ne_of_lt (Finset.mem_filter.mp iNeg.property).2
      rw [Matrix.mul_apply]
      simp [M, Aₙ, hposnz, hnegnz, add_mul, Finset.sum_add_distrib]
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [M, Aₙ, (Finset.mem_filter.mp iZero.property).2]
  -- Main equivalence rewritten in terms of `M`.
  have h_equiv_M :
      (∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * A₀).mulVec x' ≤ M.mulVec b := by
    constructor
    · rintro ⟨x, hx⟩
      rcases hlft x hx with ⟨x', hElim⟩
      refine ⟨x', ?_⟩
      simpa only [hA'_eq, hb'_eq] using hElim
    · rintro ⟨x', hxElim⟩
      have hA'ineq : A'.mulVec x' ≤ b' := by
        simpa only [hA'_eq, hb'_eq] using hxElim
      exact hright x' hA'ineq
  -- Package all existential witnesses and side conditions.
  exact ⟨κ, inferInstance, M, hM_nonneg, hM_last_zero, by simpa [A₀] using h_equiv_M⟩
end FarkasLemma

/- Original module: Farkas1 -/

open Matrix
/-
A theorem of the alternative.

Either Ax <= b has a solution, or
y >=0, y'A = 0, y'b < 0 has a solution.

We prove it using our Fourier-Motzkin elimination theorem.
-/

namespace FarkasLemma

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def Farkas1Primal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, A.mulVec x ≤  b

def Farkas1Dual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0)

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

theorem Farkas1Exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  ¬(Farkas1Primal A b ∧ Farkas1Dual A b) := by
  rintro ⟨⟨x, hAx⟩, ⟨y, hy, hyA, hyb⟩⟩
  have hyb_nonneg : 0 ≤ y ⬝ᵥ b := by
    have hdot_le : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := by
      simpa using dotProduct_le_dotProduct_of_nonneg_left hAx hy
    have hdot_eq : y ⬝ᵥ (A *ᵥ x) = 0 := by
      calc
        y ⬝ᵥ (A *ᵥ x) = (y ᵥ* A) ⬝ᵥ x := by
          simpa using Matrix.dotProduct_mulVec y A x
        _ = 0 := by simp [hyA]
    have hzero : 0 ≤ y ⬝ᵥ (A *ᵥ x) := by
      simp [hdot_eq]
    exact le_trans hzero hdot_le
  linarith

private theorem liftDual_of_fourierMotzkin {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F) (b : m → F) (M : Matrix κ m F)
    (hM_last : ∀ i, (M * A) i (Fin.last n) = 0)
    (hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j)
  (y' : κ → F)
  (hy'_nonneg : ∀ j, 0 ≤ y' j)
  (hy'_Ared : y' ᵥ* (M * (A.submatrix id Fin.castSucc)) = 0)
  (hy'_bred : y' ⬝ᵥ M.mulVec b < 0) :
  let y : m → F := M.transpose.mulVec y'
  (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0) := by
  have hy_nonneg : ∀ j, 0 ≤ (M.transpose.mulVec y') j := by
    intro j
    simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct] using
      dotProduct_nonneg_of_nonneg (hMt_nonneg j) hy'_nonneg
  have hy'_Acast : y' ᵥ* ((M * A).submatrix id Fin.castSucc) = 0 := by
    have hAred_eq : M * (A.submatrix id Fin.castSucc) = (M * A).submatrix id Fin.castSucc := by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA : y' ᵥ* (M * A) = 0 := by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul, dotProduct, hM_last]
    · intro k
      simpa [Matrix.vecMul, dotProduct] using congr_fun hy'_Acast k
  have hyA : (M.transpose.mulVec y') ᵥ* A = 0 := by
    calc
      (M.transpose.mulVec y') ᵥ* A = (y' ᵥ* M) ᵥ* A := by
        rw [Matrix.mulVec_transpose]
      _ = y' ᵥ* (M * A) := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := hy'_MA
  have hyb : (M.transpose.mulVec y') ⬝ᵥ b < 0 := by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b = (y' ᵥ* M) ⬝ᵥ b := by
        rw [Matrix.mulVec_transpose]
      _ = y' ⬝ᵥ M.mulVec b := by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0 := hy'_bred
  simpa using
    (show (∀ j, 0 ≤ (M.transpose.mulVec y') j) ∧
        ((M.transpose.mulVec y') ᵥ* A = 0) ∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg, hyA, hyb⟩)

/-!
## Farkas' Lemma
-/

theorem Farkas1Exhaust {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Farkas1Primal A b ∨ Farkas1Dual A b := by
  induction n generalizing m b with
  | zero =>
      by_cases hb : 0 ≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi : ∃ i : m, b i < 0 := by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i, lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i, hbi⟩
        classical
        let y : m → F := fun j => if j = i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i <;> simp [y, hji]
        · ext j
          exact j.elim0
        · have hyb : y ⬝ᵥ b = b i := by
            simp [y, dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP : Farkas1Primal A b
      · exact Or.inl hP
      · right
        rcases Fourier_Motzkin A b with ⟨κ, _, M, hM_nonneg, hM_last, hFM⟩
        let Ared : Matrix κ (Fin n) F := M * (A.submatrix id Fin.castSucc)
        let bred : κ → F := M.mulVec b
        have hFM' : Farkas1Primal A b ↔ Farkas1Primal (m := κ) Ared bred := by
          simpa [Farkas1Primal, Ared, bred] using hFM
        have hred_noPrimal : ¬ Farkas1Primal (m := κ) Ared bred := by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust : Farkas1Primal (m := κ) Ared bred ∨ Farkas1Dual (m := κ) Ared bred :=
          ih (m := κ) (A := Ared) (b := bred)
        have hred_dual : Farkas1Dual (m := κ) Ared bred := by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y', hy'_nonneg, hy'_Ared, hy'_bred⟩
        have hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j := by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift : Farkas1Dual A b := by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared, bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift
end FarkasLemma

/- Original module: Farkas2 -/

/-
Proving Farkas Lemma Based on the theorem of the alternative in
Farkas1.Lean
-/

open Matrix

namespace FarkasLemma2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def InCone2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b

def HasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ (vecMul y A) j) ∧ y ⬝ᵥ b < 0

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

/-!
## Reduction to Farkas1
-/

-- Matrix part of the reduction to `Farkas1`.
def farkas2RedA {n : ℕ} (A : Matrix m (Fin n) F) : Matrix (m ⊕ m ⊕ Fin n) (Fin n) F :=
  fun i j =>
    match i with
    | Sum.inl i₁ => A i₁ j
    | Sum.inr (Sum.inl i₂) => -A i₂ j
    | Sum.inr (Sum.inr k) => if k = j then (-1 : F) else 0

-- RHS part of the reduction to `Farkas1`.
def farkas2Redd {n : ℕ} (b : m → F) : (m ⊕ m ⊕ Fin n) → F :=
  fun i =>
    match i with
    | Sum.inl i₁ => b i₁
    | Sum.inr (Sum.inl i₂) => -b i₂
    | Sum.inr (Sum.inr _) => 0

-- Packed transformed data.
def farkas2_to_farkas1 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Matrix (m ⊕ m ⊕ Fin n) (Fin n) F × ((m ⊕ m ⊕ Fin n) → F) :=
  (farkas2RedA A, farkas2Redd b)

-- Shorthand for the reduced `Farkas1` primal system.
def Farkas2ReducedPrimal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Primal (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

-- Shorthand for the reduced `Farkas1` dual system.
def Farkas2ReducedDual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Dual (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

/-!
## Mapping lemmas
-/

-- Converts a reduced `Farkas1` primal witness into an `InCone2` witness.
omit [Fintype m] in
lemma farkas1_primal_to_inCone2 [Fintype m] {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hP : Farkas2ReducedPrimal A b) :
    InCone2 A b := by
  rcases hP with ⟨x, hx_le⟩
  refine ⟨x, ?_, ?_⟩
  · intro j
    have hj := hx_le (Sum.inr (Sum.inr j))
    have hj' : -x j ≤ (0 : F) := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hj
    linarith
  · ext i
    have hi₁ := hx_le (Sum.inl i)
    have hi₂ := hx_le (Sum.inr (Sum.inl i))
    have hle : A.mulVec x i ≤ b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hi₁
    have hge_neg : -(A.mulVec x i) ≤ -b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hi₂
    have hge : b i ≤ A.mulVec x i := by
      linarith
    exact le_antisymm hle hge

-- Converts a reduced `Farkas1` dual witness into a `HasDualCert2` witness.
lemma farkas1_dual_to_hasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hD : Farkas2ReducedDual A b) :
    HasDualCert2 A b := by
  rcases hD with ⟨w, hw_nonneg, hwC_zero, hwd_neg⟩
  let y₁ : m → F := fun i => w (Sum.inl i)
  let y₂ : m → F := fun i => w (Sum.inr (Sum.inl i))
  let y : m → F := y₁ - y₂
  refine ⟨y, ?_, ?_⟩
  · intro j
    have hcol0 : (w ᵥ* farkas2RedA A) j = 0 := by simpa using congr_fun hwC_zero j
    have hcol : (vecMul y A) j = w (Sum.inr (Sum.inr j)) := by
      have hsplit :
          (w ᵥ* farkas2RedA A) j =
            (vecMul y₁ A) j - (vecMul y₂ A) j - w (Sum.inr (Sum.inr j)) := by
        simp [farkas2RedA, y₁, y₂, Matrix.vecMul, dotProduct]
        ring
      have hy_split : (vecMul y A) j = (vecMul y₁ A) j - (vecMul y₂ A) j := by
        simp [y, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
      linarith [hcol0, hsplit, hy_split]
    have hj_nonneg : 0 ≤ w (Sum.inr (Sum.inr j)) := hw_nonneg (Sum.inr (Sum.inr j))
    simpa [hcol] using hj_nonneg
  · have hwd : w ⬝ᵥ farkas2Redd b = y ⬝ᵥ b := by
      calc
        w ⬝ᵥ farkas2Redd b = y₁ ⬝ᵥ b - y₂ ⬝ᵥ b := by
          simp [farkas2Redd, y₁, y₂, dotProduct]
          ring
        _ = y ⬝ᵥ b := by
          simp [y, dotProduct, Finset.sum_sub_distrib, sub_mul]
    rw [hwd] at hwd_neg
    exact hwd_neg

/-!
## Farkas' Lemma
-/

theorem farkas2_exhaustive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b := by
  have hAlt : Farkas2ReducedPrimal A b ∨ Farkas2ReducedDual A b :=
    FarkasLemma.Farkas1Exhaust (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)
  cases hAlt with
  | inl hP =>
      exact Or.inl (farkas1_primal_to_inCone2 A b hP)
  | inr hD =>
      exact Or.inr (farkas1_dual_to_hasDualCert2 A b hD)

theorem farkas2_exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  ¬(InCone2 A b ∧ HasDualCert2 A b) := by
  rintro ⟨⟨x, hx_nonneg, rfl⟩, y, hyA_nonneg, hyb_neg⟩
  have h_assoc : y ⬝ᵥ (A.mulVec x) = (vecMul y A) ⬝ᵥ x :=
    dotProduct_mulVec y A x
  have h_nonneg : 0 ≤ (vecMul y A) ⬝ᵥ x :=
    dotProduct_nonneg_of_nonneg hyA_nonneg hx_nonneg
  linarith [h_assoc, h_nonneg, hyb_neg]

theorem farkas2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b :=
  farkas2_exhaustive A b

end FarkasLemma2


/- BUNDLE COMPONENT: SteinitzSupportingFaceHelpers -/

set_option autoImplicit false

open Finset Set

namespace SteinitzSupportingFace

variable {ι V : Type*} [Fintype ι] [Fintype V]

/-- The barycentric weights representing a fixed point using a finite family. -/
def feasibleWeights (x : ι → V → ℝ) (b : V → ℝ) : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • x i = b}

omit [Fintype V] in
theorem feasibleWeights_nonempty_of_mem_convexHull [Fintype V] (x : ι → V → ℝ) (b : V → ℝ)
    (hb : b ∈ convexHull ℝ (Set.range x)) : (feasibleWeights x b).Nonempty := by
  classical
  have hc : Convex ℝ {b | (feasibleWeights x b).Nonempty} := by
    intro u hu v hv a d ha hd had
    obtain ⟨wu, hwu⟩ := hu
    obtain ⟨wv, hwv⟩ := hv
    refine ⟨fun i => a * wu i + d * wv i,
      fun i => add_nonneg (mul_nonneg ha (hwu.1 i)) (mul_nonneg hd (hwv.1 i)), ?_, ?_⟩
    · rw [sum_add_distrib, ← mul_sum, ← mul_sum, hwu.2.1, hwv.2.1]
      simpa using had
    · simp_rw [add_smul, mul_smul, sum_add_distrib, ← smul_sum]
      rw [hwu.2.2, hwv.2.2]
  apply convexHull_min ?_ hc hb
  rintro _ ⟨i, rfl⟩
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
  · intro j
    dsimp
    split_ifs <;> norm_num
  · simp
  · simp

omit [Fintype V] in
theorem isClosed_feasibleWeights [Fintype V] (x : ι → V → ℝ) (b : V → ℝ) :
    IsClosed (feasibleWeights x b) := by
  have hnonneg : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    change IsClosed (Set.Ici (0 : ι → ℝ))
    exact isClosed_Ici
  have hsum : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbary : IsClosed {w : ι → ℝ | ∑ i, w i • x i = b} :=
    isClosed_eq (by fun_prop) continuous_const
  exact hnonneg.inter (hsum.inter hbary)

theorem isCompact_feasibleWeights (x : ι → V → ℝ) (b : V → ℝ) :
    IsCompact (feasibleWeights x b) := by
  refine (isCompact_Icc : IsCompact (Icc (0 : ι → ℝ) 1)).of_isClosed_subset
    (isClosed_feasibleWeights x b) ?_
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  calc
    w i ≤ ∑ j, w j := single_le_sum (fun j _ => hw.1 j) (mem_univ i)
    _ = 1 := hw.2.1

theorem exists_maximal_weights (x : ι → V → ℝ) (b : V → ℝ) (g : ι → ℝ)
    (hW : (feasibleWeights x b).Nonempty) :
    ∃ w ∈ feasibleWeights x b,
      ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i := by
  exact (isCompact_feasibleWeights x b).exists_isMaxOn
    (f := fun w : ι → ℝ => ∑ i, w i * g i) hW (by fun_prop)


end SteinitzSupportingFace

/- BUNDLE COMPONENT: SteinitzLiftedSeparation -/

set_option autoImplicit false

open Finset Set Matrix

namespace SteinitzSupportingFace

variable {V : Type*} [Fintype V] {n : ℕ}

/-- A maximal convex combination of finitely many lifted points has a supporting
    functional whose height coefficient is strictly negative, including over
    boundary points of the base convex hull. -/
theorem maximal_weights_separator (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (w : Fin n → ℝ) (_hw : w ∈ feasibleWeights x b)
    (hmax : ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i) :
    ∃ y : Option V → ℝ, y none < 0 ∧
      ∀ i, 0 ≤ y none * (g i - ∑ j, w j * g j) +
        ∑ v, y (some v) * (x i v - b v) := by
  classical
  let t : ℝ := ∑ i, w i * g i
  let A : Matrix (Option V) (Fin n) ℝ :=
    fun j i => match j with
      | none => g i - t
      | some v => x i v - b v
  let e : Option V → ℝ := fun j => match j with
    | none => 1
    | some _ => 0
  rcases FarkasLemma2.farkas2_exhaustive A e with hprimal | hdual
  · obtain ⟨a, ha, hae⟩ := hprimal
    have hheight : ∑ i, a i * g i - (∑ i, a i) * t = 1 := by
      have h := congrFun hae none
      simp only [A, e, Matrix.mulVec, dotProduct] at h
      simp_rw [sub_mul] at h
      rw [sum_sub_distrib, ← mul_sum] at h
      simpa only [mul_comm] using h
    have hbase : ∀ v, ∑ i, a i * x i v = (∑ i, a i) * b v := by
      intro v
      have h := congrFun hae (some v)
      have h' : (∑ i, a i * x i v) - (∑ i, a i) * b v = 0 := by
        simp only [A, e, Matrix.mulVec, dotProduct] at h
        simp_rw [sub_mul] at h
        rw [sum_sub_distrib, ← mul_sum] at h
        simpa only [mul_comm] using h
      exact sub_eq_zero.mp h'
    have hsum : 0 < ∑ i, a i := by
      have hnonneg : 0 ≤ ∑ i, a i := sum_nonneg fun i _ => ha i
      by_contra hnot
      have hz : ∑ i, a i = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
      have hall : ∀ i, a i = 0 := fun i =>
        (sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hz i (mem_univ i)
      simp [hall] at hheight
    let z : Fin n → ℝ := fun i => a i / ∑ j, a j
    have hz : z ∈ feasibleWeights x b := by
      refine ⟨fun i => div_nonneg (ha i) hsum.le, ?_, ?_⟩
      · dsimp [z]
        rw [← sum_div, div_self hsum.ne']
      · ext v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        change (∑ i, (a i / ∑ j, a j) * x i v) = b v
        simp_rw [div_mul_eq_mul_div]
        rw [← sum_div, hbase v, mul_div_cancel_left₀ _ hsum.ne']
    have hzg : ∑ i, z i * g i = t + (∑ i, a i)⁻¹ := by
      dsimp [z]
      simp_rw [div_mul_eq_mul_div]
      rw [← sum_div]
      have hg : ∑ i, a i * g i = 1 + (∑ i, a i) * t := by linarith
      rw [hg, add_div, one_div, mul_div_cancel_left₀ _ hsum.ne']
      ring
    have hm := hmax z hz
    change (∑ i, z i * g i) ≤ t at hm
    rw [hzg] at hm
    exact False.elim ((not_le_of_gt (inv_pos.mpr hsum)) (by linarith))
  · obtain ⟨y, hyA, hye⟩ := hdual
    refine ⟨y, ?_, fun i => ?_⟩
    · simpa [e, dotProduct, Fintype.sum_option] using hye
    · simpa [A, t, Matrix.vecMul, dotProduct, Fintype.sum_option, add_comm] using hyA i


theorem maximal_weights_majorant (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (w : Fin n → ℝ) (hw : w ∈ feasibleWeights x b)
    (hmax : ∀ z ∈ feasibleWeights x b, (∑ i, z i * g i) ≤ ∑ i, w i * g i) :
    ∃ p : V → ℝ, ∀ i,
      g i + (∑ v, p v * x i v) ≤ (∑ j, w j * g j) + (∑ v, p v * b v) := by
  obtain ⟨y, hy, hsep⟩ := maximal_weights_separator x b g w hw hmax
  let p : V → ℝ := fun v => y (some v) / y none
  refine ⟨p, fun i => ?_⟩
  have hsum : (∑ v, y (some v) * (x i v - b v)) =
      y none * ((∑ v, p v * x i v) - ∑ v, p v * b v) := by
    simp only [mul_sub, sum_sub_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro v _
    all_goals
      dsimp [p]
      field_simp [hy.ne]
  have hprod : 0 ≤ y none *
      (g i + (∑ v, p v * x i v) - ((∑ j, w j * g j) + ∑ v, p v * b v)) := by
    have hi := hsep i
    rw [hsum] at hi
    nlinarith [hi]
  exact sub_nonpos.mp (nonpos_of_mul_nonneg_right hprod hy)


theorem exists_supporting_face (x : Fin n → V → ℝ) (b : V → ℝ) (g : Fin n → ℝ)
    (hW : (feasibleWeights x b).Nonempty) :
    ∃ p : V → ℝ, b ∈ convexHull ℝ
      (x '' {i | ∀ j, g j + (∑ v, p v * x j v) ≤ g i + (∑ v, p v * x i v)}) := by
  classical
  obtain ⟨w, hw, hmax⟩ := exists_maximal_weights x b g hW
  obtain ⟨p, hp⟩ := maximal_weights_majorant x b g w hw hmax
  let q : Fin n → ℝ := fun i => g i + ∑ v, p v * x i v
  let c : ℝ := (∑ i, w i * g i) + ∑ v, p v * b v
  have hq : ∀ i, q i ≤ c := hp
  have hsumq : ∑ i, w i * q i = c := by
    dsimp [q, c]
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    calc
      (∑ i, w i * ∑ v, p v * x i v) = ∑ v, p v * ∑ i, w i * x i v := by
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        apply sum_congr rfl
        intro i _
        ring
      _ = ∑ v, p v * b v := by
        apply sum_congr rfl
        intro v _
        have hb := congrFun hw.2.2 v
        have hb' : (∑ i, w i * x i v) = b v := by simpa using hb
        rw [hb']
  have hslack : ∑ i, w i * (c - q i) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hw.2.1, one_mul, hsumq, sub_self]
  have hsupport : ∀ i, w i ≠ 0 → q i = c := by
    intro i hi
    have hz := (sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw.1 j) (sub_nonneg.mpr (hq j)))).mp hslack i (mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hi)).symm
  let s : Finset (Fin n) := univ.filter fun i => w i ≠ 0
  have hsum : ∑ i ∈ s, w i = 1 := by
    calc
      (∑ i ∈ s, w i) = ∑ i, w i := sum_subset (filter_subset _ _)
        (fun i _ hi => by simpa [s] using hi)
      _ = 1 := hw.2.1
  have hbary : ∑ i ∈ s, w i • x i = b := by
    calc
      (∑ i ∈ s, w i • x i) = ∑ i, w i • x i := sum_subset (filter_subset _ _)
        (fun i _ hi => by
          have hz : w i = 0 := by simpa [s] using hi
          simp [hz])
      _ = b := hw.2.2
  refine ⟨p, ?_⟩
  rw [← hbary]
  apply (convex_convexHull ℝ _).sum_mem (fun i _ => hw.1 i) hsum
  intro i hi
  apply subset_convexHull
  refine ⟨i, ?_, rfl⟩
  intro j
  change q j ≤ q i
  rw [hsupport i ((mem_filter.mp hi).2)]
  exact hq j


end SteinitzSupportingFace

/- BUNDLE COMPONENT: SteinitzSupportingFaceSolution -/

set_option autoImplicit false

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (_hB : B.Nonempty) (g : (V → ℤ) → ℝ) (b : V → ℝ)
    (hb : b ∈ hull B) :
    ∃ p : V → ℝ, b ∈ hull (argmaxB B (perturb g p)) := by
  classical
  let e : Fin (Fintype.card (B : Set (V → ℤ))) ≃ (B : Set (V → ℤ)) :=
    (Fintype.equivFin (B : Set (V → ℤ))).symm
  let x : Fin (Fintype.card (B : Set (V → ℤ))) → V → ℝ := fun i => toReal (e i)
  let g' : Fin (Fintype.card (B : Set (V → ℤ))) → ℝ := fun i => g (e i)
  have hrange : Set.range x = toReal '' (B : Set (V → ℤ)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, (e i).property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm ⟨z, hz⟩, by simp [x]⟩
  have hbx : b ∈ convexHull ℝ (Set.range x) := by
    rw [hrange]
    exact hb
  have hW := SteinitzSupportingFace.feasibleWeights_nonempty_of_mem_convexHull x b hbx
  obtain ⟨p, hp⟩ := SteinitzSupportingFace.exists_supporting_face x b g' hW
  refine ⟨p, convexHull_mono ?_ hp⟩
  rintro z ⟨i, hi, rfl⟩
  refine ⟨e i, ?_, rfl⟩
  simp only [argmaxB, Finset.mem_coe, Finset.mem_filter]
  refine ⟨(e i).property, ?_⟩
  intro z hz
  have h := hi (e.symm ⟨z, hz⟩)
  simpa [x, g', perturb, pairing] using h


end AttributedSteinitz.SupportingFace

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.exists_perturb_hull_argmax {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (b : V → ℝ)
    (hb : b ∈ hull B) :
    ∃ p : V → ℝ, b ∈ hull (argmaxB B (perturb g p)) := by
  exact AttributedSteinitz.SupportingFace.solution B hB g b hb
end


namespace AttributedSteinitz.Midpoint
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.midpoint_exchange_mem_base
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T17:52:37.673914+00:00
-- url     : https://prove2.me/submissions/1ed3252a-494e-46bc-97a3-77596a4bebec



open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem base_eq_of_coordinatewise_le [Fintype V] {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hxy : ∀ w, x w ≤ y w) : x = y := by
  ext u
  by_contra hne
  have hu : 0 < (y - x) u := by
    change 0 < y u - x u
    have := hxy u
    omega
  obtain ⟨v, hv, _⟩ := hB.2 y hy x hx u hu
  change y v - x v < 0 at hv
  have := hxy v
  omega

def positiveDeviation (x y : V → ℤ) : ℤ :=
  ∑ w, max (x w - y w) 0

theorem positiveDeviation_exchange (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    positiveDeviation (x - chi u + chi v) y = positiveDeviation x y - 1 := by
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hpoint : ∀ w, max ((x - chi u + chi v) w - y w) 0 =
      max (x w - y w) 0 - (if w = u then 1 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
        if_neg huv]
      change 0 < x u - y u at hu
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
          if_neg hwu, sub_zero]
        change x v - y v < 0 at hv
        omega
      · simp [Pi.add_apply, Pi.sub_apply, chi, hwu, hwv]
  simp only [positiveDeviation, hpoint, Finset.sum_sub_distrib]
  simp

theorem sum_exchange (x : V → ℤ) (u v : V) :
    (∑ w, (x - chi u + chi v) w) = ∑ w, x w := by
  simp [Pi.add_apply, Pi.sub_apply, chi, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Pi.single_apply]

theorem base_sum_eq {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ w, x w) = ∑ w, y w := by
  classical
  let S := B.filter (fun z => (∑ w, z w) = ∑ w, x w)
  have hS : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S (fun z => positiveDeviation z y) hS
  have hzB : z ∈ B := (Finset.mem_filter.mp hz).1
  have hzsum : (∑ w, z w) = ∑ w, x w := (Finset.mem_filter.mp hz).2
  have hzle : ∀ u, z u ≤ y u := by
    intro u
    by_contra hnot
    have hu : 0 < (z - y) u := by
      change 0 < z u - y u
      omega
    obtain ⟨v, hv, hz'⟩ := hB.2 z hzB y hy u hu
    have hmem : z - chi u + chi v ∈ S :=
      Finset.mem_filter.mpr ⟨hz', (sum_exchange z u v).trans hzsum⟩
    have hmin' := hmin _ hmem
    rw [positiveDeviation_exchange z y u v hu hv] at hmin'
    omega
  have hzy : z = y := base_eq_of_coordinatewise_le hB hzB hy hzle
  subst z
  exact hzsum.symm


end SteinitzExchange.Extension

set_option autoImplicit false

open Set

namespace SteinitzCoordinator

/-- Symmetric basis exchange, extracted from the existing circuit-cocircuit API.
This is a local draft until its exact-environment compiler check succeeds. -/
theorem symmetric_basis_exchange {α : Type*} (M : Matroid α)
    {X Y : Set α} (hX : M.IsBase X) (hY : M.IsBase Y)
    {e : α} (he : e ∈ X \ Y) :
    ∃ f ∈ Y \ X,
      M.IsBase (insert f (X \ {e})) ∧ M.IsBase (insert e (Y \ {f})) := by
  have heE : e ∈ M.E := hX.subset_ground he.1
  have hC := hY.fundCircuit_isCircuit heE he.2
  have hK := hX.compl_closure_sdiff_singleton_isCocircuit he.1
  have heK : e ∈ M.E \ M.closure (X \ {e}) :=
    ⟨heE, hX.indep.notMem_closure_sdiff_of_mem he.1⟩
  have hn := hC.isCocircuit_inter_nontrivial hK
    ⟨e, M.mem_fundCircuit e Y, heK⟩
  obtain ⟨f, hf, hfe⟩ := hn.exists_ne e
  have hfY : f ∈ Y := by
    have h := M.fundCircuit_subset_insert e Y hf.1
    rcases h with h | h
    · exact (hfe h).elim
    · exact h
  have hfX : f ∉ X := by
    intro h
    exact hf.2.2 (M.subset_closure (X \ {e})
      (sdiff_subset.trans hX.subset_ground) ⟨h, hfe⟩)
  have hecl : e ∈ M.closure Y := by rwa [hY.closure_eq]
  have hi : M.Indep (insert e Y \ {f}) :=
    (hY.indep.mem_fundCircuit_iff hecl he.2).mp hf.1
  refine ⟨f, ⟨hfY, hfX⟩,
    hX.exchange_base_of_notMem_closure he.1 hf.2.2 hf.2.1, ?_⟩
  have hb := hY.exchange_isBase_of_indep' hfY he.2 hi
  simpa only [← insert_sdiff_singleton_comm hfe.symm] using hb


end SteinitzCoordinator

open Set

namespace SteinitzCoordinator

variable {V : Type*} [DecidableEq V]

def cloneFiber (S : Set (V × ℕ)) (i : V) : Set ℕ :=
  {k | (i, k) ∈ S}

noncomputable def cloneCount (S : Set (V × ℕ)) (i : V) : ℤ :=
  (cloneFiber S i).ncard

omit [DecidableEq V] in
lemma cloneFiber_finite [DecidableEq V] {S : Set (V × ℕ)} (hS : S.Finite) (i : V) :
    (cloneFiber S i).Finite := by
  exact hS.preimage (fun _ _ _ _ h => (Prod.mk.inj h).2)

lemma cloneFiber_insert (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (insert (u,k) S) i =
      if i = u then insert k (cloneFiber S i) else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneFiber_delete (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (S \ {(u,k)}) i =
      if i = u then cloneFiber S i \ {k} else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneCount_insert {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∉ S) (i : V) :
    cloneCount (insert (u,k) S) i = cloneCount S i + if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_insert]
  split_ifs with h
  · subst i
    rw [Set.ncard_insert_of_notMem (show k ∉ cloneFiber S u from hk)
      (cloneFiber_finite hS u)]
    simp
  · simp

lemma cloneCount_delete {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S) (i : V) :
    cloneCount (S \ {(u,k)}) i = cloneCount S i - if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_delete]
  split_ifs with h
  · subst i
    have hn := Set.ncard_sdiff_singleton_add_one
      (show k ∈ cloneFiber S u from hk) (cloneFiber_finite hS u)
    omega
  · simp

lemma cloneCount_mono {S T : Set (V × ℕ)} (hT : T.Finite)
    (hST : S ⊆ T) (i : V) : cloneCount S i ≤ cloneCount T i := by
  unfold cloneCount
  exact_mod_cast Set.ncard_le_ncard (s := cloneFiber S i) (t := cloneFiber T i)
    (fun k hk => hST hk) (cloneFiber_finite hT i)

lemma exists_clone_difference {S T : Set (V × ℕ)} (hS : S.Finite)
    (i : V) (h : cloneCount S i < cloneCount T i) :
    ∃ k, (i,k) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T i ⊆ cloneFiber S i := by
    intro k hk
    by_contra hkS
    exact hn ⟨k,hk,hkS⟩
  have hc := Set.ncard_le_ncard hsub (cloneFiber_finite hS i)
  unfold cloneCount at h
  omega

lemma exists_clone_same_coordinate {S T : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S \ T)
    (h : cloneCount S u ≤ cloneCount T u) :
    ∃ l, (u,l) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T u ⊆ cloneFiber S u \ {k} := by
    intro l hl
    refine ⟨?_, ?_⟩
    · by_contra hls
      exact hn ⟨l,hl,hls⟩
    · intro hlk
      have heq : l = k := Set.mem_singleton_iff.mp hlk
      change (u,l) ∈ T at hl
      rw [heq] at hl
      exact hk.2 hl
  have hc := Set.ncard_le_ncard hsub ((cloneFiber_finite hS u).sdiff)
  have hd := Set.ncard_sdiff_singleton_add_one
    (show k ∈ cloneFiber S u from hk.1) (cloneFiber_finite hS u)
  unfold cloneCount at h
  omega

lemma cloneCount_swap {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) (i : V) :
    cloneCount (insert (v,l) (S \ {(u,k)})) i =
      cloneCount S i - (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
  rw [cloneCount_insert (hS.sdiff) v l (fun h => hl h.1) i,
    cloneCount_delete hS u k hk i]

variable [Fintype V]

def cloneLift (n : V → ℕ) : Finset (V × ℕ) :=
  Finset.univ.biUnion (fun i => (Finset.range (n i)).image (fun k => (i,k)))

@[simp] lemma mem_cloneLift (n : V → ℕ) (i : V) (k : ℕ) :
    (i,k) ∈ cloneLift n ↔ k < n i := by
  simp [cloneLift, Prod.mk.injEq]

lemma cloneFiber_lift (n : V → ℕ) (i : V) :
    cloneFiber (cloneLift n : Set (V × ℕ)) i = (Finset.range (n i) : Set ℕ) := by
  ext k
  simp [cloneFiber]

@[simp] lemma cloneCount_lift (n : V → ℕ) (i : V) :
    cloneCount (cloneLift n : Set (V × ℕ)) i = n i := by
  unfold cloneCount
  rw [cloneFiber_lift, Set.ncard_coe_finset, Finset.card_range]

end SteinitzCoordinator

open Set
open SteinitzExchange.Extension

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def shiftedCount (m : V → ℤ) (S : Set (V × ℕ)) : V → ℤ :=
  fun i => cloneCount S i + m i

noncomputable def cloneBase (m : V → ℤ) (B : Finset (V → ℤ))
    (S : Set (V × ℕ)) : Prop := S.Finite ∧ shiftedCount m S ∈ B

omit [Fintype V] in
lemma shiftedCount_swap [Fintype V] (m : V → ℤ) {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) :
    shiftedCount m (insert (v,l) (S \ {(u,k)})) =
      shiftedCount m S - chi u + chi v := by
  ext i
  simp only [shiftedCount, Pi.add_apply, Pi.sub_apply]
  rw [cloneCount_swap hS u v k l hk hl i]
  simp only [chi, Pi.single_apply]
  split_ifs <;> omega

lemma cloneBase_exchange (m : V → ℤ) {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) : Matroid.ExchangeProperty (cloneBase m B) := by
  intro S T hS hT a ha
  rcases a with ⟨u,k⟩
  by_cases hle : cloneCount S u ≤ cloneCount T u
  · obtain ⟨l, hl⟩ := exists_clone_same_coordinate hS.1 u k ha hle
    refine ⟨(u,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u u k l ha.1 hl.2]
    simpa using hS.2
  · have hu : 0 < (shiftedCount m S - shiftedCount m T) u := by
      simp only [shiftedCount, Pi.sub_apply]
      omega
    obtain ⟨v, hv, hb⟩ := hB.2 _ hS.2 _ hT.2 u hu
    have hlt : cloneCount S v < cloneCount T v := by
      simp only [shiftedCount, Pi.sub_apply] at hv
      omega
    obtain ⟨l, hl⟩ := exists_clone_difference hS.1 v hlt
    refine ⟨(v,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u v k l ha.1 hl.2]
    exact hb

lemma shiftedCount_lift (m x : V → ℤ) (hx : ∀ i, m i ≤ x i) :
    shiftedCount m (cloneLift (fun i => (x i - m i).toNat) : Set (V × ℕ)) = x := by
  ext i
  simp only [shiftedCount, cloneCount_lift]
  have := hx i
  omega

/-- Symmetric exchange for an integral base set with an explicit coordinatewise lower bound.
No new axioms: finite integer vectors are expanded into finite bases on a countable clone ground. -/
theorem base_symmetric_exchange_with_lower_bound
    (m : V → ℤ) {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (hm : ∀ x ∈ B, ∀ i, m i ≤ x i)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let X : Set (V × ℕ) := cloneLift (fun i => (x i - m i).toNat)
  let Y : Set (V × ℕ) := cloneLift (fun i => (y i - m i).toNat)
  have hXfin : X.Finite := Finset.finite_toSet _
  have hYfin : Y.Finite := Finset.finite_toSet _
  have hXcount : shiftedCount m X = x := shiftedCount_lift m x (hm x hx)
  have hYcount : shiftedCount m Y = y := shiftedCount_lift m y (hm y hy)
  have hXB : cloneBase m B X := ⟨hXfin, hXcount.symm ▸ hx⟩
  have hYB : cloneBase m B Y := ⟨hYfin, hYcount.symm ▸ hy⟩
  let M : Matroid (V × ℕ) := Matroid.ofExistsFiniteIsBase Set.univ (cloneBase m B)
    ⟨X, hXB, hXfin⟩ (cloneBase_exchange m hB) (fun _ _ => Set.subset_univ _)
  have hXM : M.IsBase X := hXB
  have hYM : M.IsBase Y := hYB
  let k : ℕ := (y u - m u).toNat
  have hk : (u,k) ∈ X \ Y := by
    have hxu := hm x hx u
    have hyu := hm y hy u
    change 0 < x u - y u at hu
    simp only [X, Y, Set.mem_sdiff, Finset.mem_coe, mem_cloneLift, k]
    omega
  obtain ⟨⟨v,l⟩, hl, hbX, hbY⟩ := symmetric_basis_exchange M hXM hYM hk
  have hv : (x - y) v < 0 := by
    have hxv := hm x hx v
    have hyv := hm y hy v
    simp only [X, Y, Set.mem_sdiff, Finset.mem_coe, mem_cloneLift] at hl
    change x v - y v < 0
    omega
  change cloneBase m B (insert (v,l) (X \ {(u,k)})) at hbX
  change cloneBase m B (insert (u,k) (Y \ {(v,l)})) at hbY
  have hfirst := hbX.2
  have hsecond := hbY.2
  rw [shiftedCount_swap m hXfin u v k l hk.1 hl.2, hXcount] at hfirst
  rw [shiftedCount_swap m hYfin v u l k hl.1 hk.2, hYcount] at hsecond
  refine ⟨v,hv,hfirst,?_⟩
  convert hsecond using 1 ; abel

theorem base_symmetric_exchange {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let m : V → ℤ := fun i => B.inf' hB.1 (fun z => z i)
  apply base_symmetric_exchange_with_lower_bound m hB _ hx hy u hu
  intro z hz i
  exact Finset.inf'_le (fun a => a i) hz


end SteinitzCoordinator


open scoped BigOperators

namespace SteinitzExchange.Extension

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) : ι → ℝ :=
  fun i => w i - (if i = a then ε else 0) - (if i = b then ε else 0) +
    (if i = a' then ε else 0) + (if i = b' then ε else 0)

omit [Fintype ι] in
theorem transferWeights_nonneg [Fintype ι] (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    ∀ i, 0 ≤ transferWeights w a b a' b' ε i := by
  intro i
  have hp : 0 ≤ (if i = a' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  have hq : 0 ≤ (if i = b' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  unfold transferWeights
  by_cases hia : i = a
  · subst i
    simp only [if_neg hab, ite_true]
    linarith
  · by_cases hib : i = b
    · subst i
      simp only [if_neg hia, ite_true]
      linarith
    · simp only [if_neg hia, if_neg hib]
      have := hw i
      linarith

theorem sum_transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i) = ∑ i, w i := by
  simp only [transferWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

theorem weighted_sum_transfer {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i • p i) =
      (∑ i, w i • p i) - ε • p a - ε • p b + ε • p a' + ε • p b' := by
  simp [transferWeights, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ite_smul]

theorem transferWeights_mem_stdSimplex (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : w ∈ stdSimplex ℝ ι) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    transferWeights w a b a' b' ε ∈ stdSimplex ℝ ι :=
  ⟨transferWeights_nonneg w a b a' b' ε hw.1 hab he hea heb,
    (sum_transferWeights w a b a' b' ε).trans hw.2⟩

theorem barycenter_transfer_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ)
    (hp : p a' + p b' = p a + p b) :
    (∑ i, transferWeights w a b a' b' ε i • p i) = ∑ i, w i • p i := by
  rw [weighted_sum_transfer]
  have heq := congrArg (fun z => ε • z) hp
  simp only [smul_add] at heq
  calc
    _ = (∑ i, w i • p i) - (ε • p a + ε • p b) +
        (ε • p a' + ε • p b') := by abel
    _ = _ := by rw [heq]; exact sub_add_cancel _ _

end Weights

section Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

def integerEnergy (x : V → ℤ) : ℤ := ∑ w, (x w) ^ 2

theorem integerEnergy_exchange (a b : V → ℤ) (u v : V) (huv : u ≠ v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) -
      integerEnergy a - integerEnergy b =
        -2 * (a u - b u) + 2 * (a v - b v) + 4 := by
  have hpoint : ∀ w,
      ((a - chi u + chi v) w) ^ 2 + ((b + chi u - chi v) w) ^ 2 -
          (a w) ^ 2 - (b w) ^ 2 =
        (if w = u then -2 * (a u - b u) + 2 else 0) +
        (if w = v then 2 * (a v - b v) + 2 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp [chi, huv] ; ring
    · by_cases hwv : w = v
      · subst w
        simp [chi, hwu] ; ring
      · simp [chi, hwu, hwv]
  unfold integerEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp ; ring

theorem integerEnergy_exchange_lt (a b : V → ℤ) (u v : V)
    (hu : b u + 2 ≤ a u) (hv : a v < b v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) <
      integerEnergy a + integerEnergy b := by
  have huv : u ≠ v := by intro h; subst v; omega
  have he := integerEnergy_exchange a b u v huv
  omega

end Energy

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

section ConvexWeights

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]

theorem convexHull_range_exists_weights (p : ι → E) {c : E}
    (hc : c ∈ convexHull ℝ (Set.range p)) :
    ∃ w : ι → ℝ, w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = c := by
  have hconv : Convex ℝ {z : E | ∃ w : ι → ℝ,
      w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = z} := by
    rintro x ⟨w, hw, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • w + b • v, (convex_stdSimplex ℝ ι) hw hv ha hb hab, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum]
  apply convexHull_min ?_ hconv hc
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
  simp [Pi.single_apply, ite_smul]

end ConvexWeights

section BaseWeights

variable {V : Type*} [Fintype V] [DecidableEq V]

def baseBarycenter (A : Finset (V → ℤ)) (w : A → ℝ) : V → ℝ :=
  ∑ a : A, w a • toReal a.1

def weightedEnergy (A : Finset (V → ℤ)) (w : A → ℝ) : ℝ :=
  ∑ a : A, w a * (integerEnergy a.1 : ℝ)

omit [DecidableEq V] in
theorem hull_exists_weights [DecidableEq V] (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c := by
  have hr : Set.range (fun a : A => toReal a.1) =
      toReal '' (A : Set (V → ℤ)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  apply convexHull_range_exists_weights (fun a : A => toReal a.1)
  simpa only [hr, hull] using hc

theorem hull_coordinate_sum_eq (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (a : V → ℤ) (ha : a ∈ A) {c : V → ℝ} (hc : c ∈ hull A) :
    (∑ v, c v) = ((∑ v, a v : ℤ) : ℝ) := by
  obtain ⟨w, hw, hbar⟩ := hull_exists_weights A hc
  rw [← hbar]
  simp only [baseBarycenter, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Int.cast_sum]
  have hs : ∀ b : A, (∑ v, b.1 v) = ∑ v, a v :=
    fun b => base_sum_eq hA b.2 ha
  simp_rw [hs]
  rw [← Finset.sum_mul, hw.2, one_mul]

theorem exists_minimal_energy_weights (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c ∧
      ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
        weightedEnergy A w ≤ weightedEnergy A v := by
  let K : Set (A → ℝ) := stdSimplex ℝ A ∩ {w | baseBarycenter A w = c}
  have hbar : Continuous (baseBarycenter A) := by unfold baseBarycenter; fun_prop
  have henergy : Continuous (weightedEnergy A) := by unfold weightedEnergy; fun_prop
  have hcompact : IsCompact K :=
    (isCompact_stdSimplex ℝ A).inter_right (isClosed_eq hbar continuous_const)
  obtain ⟨w, hw, hbarw⟩ := hull_exists_weights A hc
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn ⟨w, hw, hbarw⟩ henergy.continuousOn
  exact ⟨v, hv.1, hv.2, fun z hz hbarz => hmin ⟨hz, hbarz⟩⟩

def SymmetricBaseExchange (A : Finset (V → ℤ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ u : V, b u < a u →
    ∃ v : V, a v < b v ∧ a - chi u + chi v ∈ A ∧ b + chi u - chi v ∈ A

theorem minimal_energy_support_close (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (w : A → ℝ)
    (hw : w ∈ stdSimplex ℝ A) (hbar : baseBarycenter A w = c)
    (hmin : ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
      weightedEnergy A w ≤ weightedEnergy A v) :
    ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1 := by
  classical
  intro a b ha hb u
  by_contra hnot
  have hu : b.1 u + 2 ≤ a.1 u := by omega
  obtain ⟨v, hv, ha', hb'⟩ := hA a.1 a.2 b.1 b.2 u (by omega)
  let a' : A := ⟨a.1 - chi u + chi v, ha'⟩
  let b' : A := ⟨b.1 + chi u - chi v, hb'⟩
  let ε := min (w a) (w b)
  have he : 0 < ε := lt_min ha hb
  have hab : a ≠ b := by intro h; subst b; omega
  let w' := transferWeights w a b a' b' ε
  have hw' : w' ∈ stdSimplex ℝ A :=
    transferWeights_mem_stdSimplex w a b a' b' ε hw hab (le_of_lt he)
      (min_le_left _ _) (min_le_right _ _)
  have hp : toReal a'.1 + toReal b'.1 = toReal a.1 + toReal b.1 := by
    ext z
    simp [a', b', toReal]
  have hbar' : baseBarycenter A w' = c := by
    change (∑ i : A, transferWeights w a b a' b' ε i • toReal i.1) = c
    rw [barycenter_transfer_eq w (fun i : A => toReal i.1) a b a' b' ε hp]
    exact hbar
  have henergy : (integerEnergy a'.1 : ℝ) + integerEnergy b'.1 <
      integerEnergy a.1 + integerEnergy b.1 := by
    exact_mod_cast integerEnergy_exchange_lt a.1 b.1 u v hu hv
  have hdrop := mul_lt_mul_of_pos_left henergy he
  have htransfer : weightedEnergy A w' = weightedEnergy A w -
      ε * integerEnergy a.1 - ε * integerEnergy b.1 +
      ε * integerEnergy a'.1 + ε * integerEnergy b'.1 := by
    simpa only [weightedEnergy, w', smul_eq_mul] using
      weighted_sum_transfer w (fun i : A => (integerEnergy i.1 : ℝ)) a b a' b' ε
  have hcontr := hmin w' hw' hbar'
  rw [htransfer] at hcontr
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem balanced_support_mem_integer_box [Fintype V] [DecidableEq V] (A : Finset (V → ℤ))
    {c : V → ℝ} (w : A → ℝ) (hw : w ∈ stdSimplex ℝ A)
    (hbar : baseBarycenter A w = c)
    (hclose : ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    ∀ a : A, 0 < w a → ∀ u, lo u ≤ a.1 u ∧ a.1 u ≤ hi u := by
  classical
  intro a ha u
  have hcoord : (∑ b : A, w b * (b.1 u : ℝ)) = c u := by
    simpa [baseBarycenter, toReal, Finset.sum_apply] using congrFun hbar u
  constructor
  · by_contra hnot
    have hal : a.1 u < lo u := by omega
    have hle : ∀ b : A, w b * (b.1 u : ℝ) ≤ w b * (lo u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : b.1 u ≤ lo u := by have := hclose b a hb ha u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (b.1 u : ℝ)) < ∑ b : A, w b * (lo u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hal) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hlo u)) hlt
  · by_contra hnot
    have hai : hi u < a.1 u := by omega
    have hle : ∀ b : A, w b * (hi u : ℝ) ≤ w b * (b.1 u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : hi u ≤ b.1 u := by have := hclose a b ha hb u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (hi u : ℝ)) < ∑ b : A, w b * (b.1 u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hai) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hhi u)) hlt

theorem symmetricBaseExchange_hull_box (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (hc : c ∈ hull A)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    c ∈ hull (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u)) := by
  classical
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hc
  have hclose := minimal_energy_support_close A hA w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    have hnonpos : w a ≤ 0 := le_of_not_gt (by simpa [t] using hnot)
    exact le_antisymm hnonpos (hw.1 a)
  have hsum : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  have hbar' : ∑ a ∈ t, w a • toReal a.1 = c := by
    rw [← hbar]
    unfold baseBarycenter
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    simp [hout a hnot]
  have hmem : t.centerMass w (fun a : A => toReal a.1) ∈
      convexHull ℝ (toReal '' (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u) :
        Set (V → ℤ))) := by
    apply t.centerMass_mem_convexHull (fun a _ => hw.1 a) (by rw [hsum]; norm_num)
    intro a ha
    exact ⟨a.1, Finset.mem_filter.mpr ⟨a.2, hbox a (by simpa [t] using ha)⟩, rfl⟩
  rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, hbar'] at hmem
  exact hmem


end BaseWeights

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq V] in
theorem binary_complement_of_overlap_zero [DecidableEq V] (r a b : V → ℤ)
    (_hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (ha : ∀ v, 0 ≤ a v ∧ a v ≤ r v)
    (hb : ∀ v, 0 ≤ b v ∧ b v ≤ r v)
    (hsum : (∑ v, a v) + (∑ v, b v) = ∑ v, r v)
    (hoverlap : (∑ v, a v * b v) = 0) :
    ∀ v, a v + b v = r v := by
  have hprod : ∀ v, a v * b v = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (ha v).1 (hb v).1)).mp hoverlap
    exact fun v => h v (Finset.mem_univ v)
  have hle : ∀ v, a v + b v ≤ r v := by
    intro v
    rcases mul_eq_zero.mp (hprod v) with h | h <;>
      have := ha v <;> have := hb v <;> omega
  have heq : (∑ v, (a v + b v)) = ∑ v, r v := by
    rw [Finset.sum_add_distrib]
    exact hsum
  have h := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp heq
  exact fun v => h v (Finset.mem_univ v)

omit [DecidableEq ι] in
/-- Rank at most two: half marginals force complementary support vectors. -/
theorem binary_half_marginals_complement [DecidableEq ι] (r : V → ℤ) (p : ι → V → ℤ)
    (k : ℤ) (hk : k ≤ 2)
    (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (hp : ∀ i v, 0 ≤ p i v ∧ p i v ≤ r v)
    (hsum : ∀ i, (∑ v, p i v) = k)
    (hrsum : (∑ v, r v) = 2 * k)
    (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι)
    (hmean : ∀ v, (∑ i, w i * (p i v : ℝ)) = (r v : ℝ) / 2) :
    ∃ a b : ι, 0 < w a ∧ 0 < w b ∧ ∀ v, p a v + p b v = r v := by
  classical
  have haex : ∃ a, 0 < w a := by
    by_contra h
    push Not at h
    have hnonpos : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hw.2] at hnonpos
    norm_num at hnonpos
  obtain ⟨a, ha⟩ := haex
  let overlap : ι → ℤ := fun b => ∑ v, p a v * p b v
  have hoverlap_nonneg : ∀ b, 0 ≤ overlap b :=
    fun b => Finset.sum_nonneg (fun v _ => mul_nonneg (hp a v).1 (hp b v).1)
  have har : ∀ v, p a v * r v = p a v := by
    intro v
    have hrv := hr v
    have hav := hp a v
    have hcases : r v = 0 ∨ r v = 1 := by omega
    rcases hcases with h | h
    · have hpa : p a v = 0 := by omega
      simp [hpa]
    · simp [h]
  have hself : overlap a = k := by
    change (∑ v, p a v * p a v) = k
    rw [← hsum a]
    apply Finset.sum_congr rfl
    intro v _
    have hrv := hr v
    have hav := hp a v
    have hcases : p a v = 0 ∨ p a v = 1 := by omega
    rcases hcases with h | h <;> simp [h]
  have hmean_overlap : (∑ b, w b * (overlap b : ℝ)) = (k : ℝ) / 2 := by
    calc
      _ = ∑ v, (p a v : ℝ) * (∑ b, w b * (p b v : ℝ)) := by
        simp only [overlap, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ v, (p a v : ℝ) * ((r v : ℝ) / 2) := by simp_rw [hmean]
      _ = (∑ v, (p a v : ℝ)) / 2 := by
        simp_rw [← mul_div_assoc, ← Int.cast_mul, har]
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ = (k : ℝ) / 2 := by rw [← Int.cast_sum, hsum a]
  have hbex : ∃ b, 0 < w b ∧ overlap b = 0 := by
    by_contra h
    push Not at h
    have hle : ∀ b, w b ≤ w b * (overlap b : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : (1 : ℤ) ≤ overlap b := by
          have := hoverlap_nonneg b
          have := h b hb
          omega
        have hbr : (1 : ℝ) ≤ overlap b := by exact_mod_cast hbi
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hbr (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hsum_le := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hle b)
    rw [hw.2, hmean_overlap] at hsum_le
    have hkreal : (2 : ℝ) ≤ k := by linarith
    have hkint : (2 : ℤ) ≤ k := by exact_mod_cast hkreal
    have hk2 : k = 2 := le_antisymm hk hkint
    have hlt : (∑ b, w b) < ∑ b, w b * (overlap b : ℝ) := by
      apply Finset.sum_lt_sum (fun b _ => hle b)
      refine ⟨a, Finset.mem_univ a, ?_⟩
      rw [hself, hk2]
      norm_num
      linarith
    rw [hw.2, hmean_overlap, hk2] at hlt
    norm_num at hlt
  obtain ⟨b, hb, hab⟩ := hbex
  refine ⟨a, b, ha, hb, binary_complement_of_overlap_zero r (p a) (p b)
    hr (hp a) (hp b) ?_ hab⟩
  rw [hsum a, hsum b, hrsum]
  omega


end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem integralBase_symmetric (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A) :
    SymmetricBaseExchange A := by
  intro a ha b hb u hu
  obtain ⟨v, hv, hav, hbv⟩ := SteinitzCoordinator.base_symmetric_exchange hA ha hb u
    (by simpa only [Pi.sub_apply, sub_pos] using hu)
  exact ⟨v, by simpa only [Pi.sub_apply, sub_neg] using hv, hav, hbv⟩

theorem toReal_mem_hull_iff_checked (A : Finset (V → ℤ))
    (hA : IsIntegralBaseSet A) (x : V → ℤ) : toReal x ∈ hull A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    have hb := symmetricBaseExchange_hull_box A (integralBase_symmetric A hA) hx x x
      (fun _ => le_rfl) (fun _ => le_rfl)
    have hn : (toReal '' (A.filter (fun a => ∀ u, x u ≤ a u ∧ a u ≤ x u) :
        Set (V → ℤ))).Nonempty := (convexHull_nonempty_iff).mp ⟨toReal x, hb⟩
    rcases hn with ⟨z, a, ha, _⟩
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp ha
    have he : a = x := funext (fun u => le_antisymm (hax u).2 (hax u).1)
    exact he ▸ haA
  · intro hx
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩


/-- The substantial convex-geometric core: a midpoint at lattice distance four
has a complementary pair in the integral base set containing that midpoint. -/
theorem base_midpoint_complement (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hxySum : (∑ v, x v) = ∑ v, y v)
    (hxy : (∑ v, |x v - y v|) = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = x + y ∧
      ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v) := by
  classical
  let c : V → ℝ := (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y
  let lo : V → ℤ := fun v => (x v + y v) / 2
  let hi : V → ℤ := fun v => x v + y v - lo v
  let r : V → ℤ := fun v => x v + y v - 2 * lo v
  let k : ℤ := (∑ v, x v) - ∑ v, lo v
  have hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1 := by
    intro v
    dsimp [r, lo]
    omega
  have hlo : ∀ v, (lo v : ℝ) ≤ c v := by
    intro v
    have hdiv : 2 * lo v ≤ x v + y v := by dsimp [lo]; omega
    have hdivR : 2 * (lo v : ℝ) ≤ (x v : ℝ) + y v := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hhi : ∀ v, c v ≤ (hi v : ℝ) := by
    intro v
    have hdiv : x v + y v ≤ 2 * hi v := by dsimp [hi, lo]; omega
    have hdivR : (x v : ℝ) + y v ≤ 2 * (hi v : ℝ) := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hsumc : (∑ v, c v) = ((∑ v, x v : ℤ) : ℝ) := by
    simp only [c, Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hxySum]
    ring
  have hsumA : ∀ a : A, (∑ v, a.1 v) = ∑ v, x v := by
    intro a
    have he := (hull_coordinate_sum_eq A hA a.1 a.2 hm).symm.trans hsumc
    exact_mod_cast he
  have hrsum : (∑ v, r v) = 2 * k := by
    simp only [r, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← hxySum, k]
    ring
  have hrle : ∀ v, r v ≤ |x v - y v| := by
    intro v
    by_cases he : x v = y v
    · dsimp [r, lo]
      rw [he]
      simp only [sub_self, abs_zero]
      omega
    · have habs : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr he)
      have := hr v
      omega
  have hk : k ≤ 2 := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hrle v)
    rw [hrsum, hxy] at h
    omega
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hm
  have hclose := minimal_energy_support_close A (integralBase_symmetric A hA) w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hpos : ∀ a : t, 0 < w a.1 := by intro a; simpa [t] using a.2
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    exact le_antisymm (le_of_not_gt (by simpa [t] using hnot)) (hw.1 a)
  have hsumt : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  let wt : t → ℝ := fun a => w a.1
  let p : t → V → ℤ := fun a v => a.1.1 v - lo v
  have hwt : wt ∈ stdSimplex ℝ t :=
    ⟨fun a => hw.1 a.1, by simpa only [wt, Finset.sum_coe_sort] using hsumt⟩
  have hp : ∀ a v, 0 ≤ p a v ∧ p a v ≤ r v := by
    intro a v
    have h := hbox a.1 (hpos a) v
    dsimp [p, hi, r] at *
    omega
  have hpsum : ∀ a, (∑ v, p a v) = k := by
    intro a
    simp only [p, Finset.sum_sub_distrib, hsumA, k]
  have hmean : ∀ v, (∑ a, wt a * (p a v : ℝ)) = (r v : ℝ) / 2 := by
    intro v
    have hcoord : (∑ a : A, w a * (a.1 v : ℝ)) = c v := by
      simpa [baseBarycenter, toReal, Finset.sum_apply, c] using congrFun hbar v
    have hcoordt : (∑ a ∈ t, w a * (a.1 v : ℝ)) = c v := by
      rw [← hcoord]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ hnot
      simp [hout a hnot]
    have hcoordt' : (∑ a : t, wt a * (a.1.1 v : ℝ)) = c v := by
      change (∑ a : t, w a.1 * (a.1.1 v : ℝ)) = c v
      exact (Finset.sum_coe_sort t (fun a : A => w a * (a.1 v : ℝ))).trans hcoordt
    calc
      _ = (∑ a : t, wt a * (a.1.1 v : ℝ)) - (∑ a : t, wt a) * (lo v : ℝ) := by
        simp [p, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = c v - (lo v : ℝ) := by rw [hcoordt', hwt.2, one_mul]
      _ = (r v : ℝ) / 2 := by simp [c, r, toReal]; ring
  obtain ⟨a, b, ha, hb, hab⟩ :=
    binary_half_marginals_complement r p k hk hr hp hpsum hrsum wt hwt hmean
  refine ⟨a.1.1, a.1.2, b.1.1, b.1.2, ?_, ?_⟩
  · ext v
    have h := hab v
    dsimp [p, r] at h
    change a.1.1 v + b.1.1 v = x v + y v
    omega
  · intro v
    have h := hbox a.1 (hpos a) v
    have hlow : min (x v) (y v) ≤ lo v := by dsimp [lo]; omega
    have hhigh : hi v ≤ max (x v) (y v) := by dsimp [hi, lo]; omega
    exact ⟨hlow.trans h.1, h.2.trans hhigh⟩


end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem int_nonneg_sum_one_single (p : V → ℤ) (hp : ∀ v, 0 ≤ p v)
    (hs : (∑ v, p v) = 1) : ∃ u, ∀ v, p v = if v = u then 1 else 0 := by
  classical
  have hex : ∃ u, 0 < p u := by
    by_contra h
    push Not at h
    have hz : ∀ v, p v = 0 := fun v => le_antisymm (h v) (hp v)
    simp [hz] at hs
  obtain ⟨u, hu⟩ := hex
  have hle : p u ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun v _ => hp v) (Finset.mem_univ u)
  have hpu : p u = 1 := by omega
  have herase : (∑ v ∈ Finset.univ.erase u, p v) = 0 := by
    have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ u)
    rw [hs, hpu] at h
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ Finset.univ.erase u) => hp v)).mp herase
  refine ⟨u, fun v => ?_⟩
  by_cases hv : v = u
  · subst v
    simp [hpu]
  · simp [hv, hz v (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)]

omit [DecidableEq V] in
theorem l1_eq_twice_positiveDeviation [DecidableEq V] (x y : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, y v) :
    (∑ v, |x v - y v|) = 2 * positiveDeviation x y := by
  have hpoint : ∀ v, |x v - y v| = 2 * max (x v - y v) 0 - (x v - y v) := by
    intro v
    by_cases h : 0 ≤ x v - y v
    · rw [abs_of_nonneg h, max_eq_left h]
      omega
    · have h' : x v - y v ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [abs_of_nonpos h', max_eq_right h']
      omega
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs,
    sub_self, sub_zero]
  rfl

omit [DecidableEq V] in
theorem l1_pos_of_ne [DecidableEq V] (x y : V → ℤ) (hne : x ≠ y) : 0 < ∑ v, |x v - y v| := by
  have hex : ∃ v, x v ≠ y v := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨v, hv⟩ := hex
  have hpos : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr hv)
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (fun w _ => abs_nonneg (x w - y w)) (Finset.mem_univ v))

theorem l1_two_unit_exchange (x a : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, a v) (hd : (∑ v, |x v - a v|) = 2) :
    ∃ u v, 0 < (x - a) u ∧ (x - a) v < 0 ∧ a = x - chi u + chi v := by
  have hp : positiveDeviation x a = 1 := by
    have h := l1_eq_twice_positiveDeviation x a hs
    omega
  have hq : positiveDeviation a x = 1 := by
    have h := l1_eq_twice_positiveDeviation a x hs.symm
    have hd' : (∑ v, |a v - x v|) = 2 := by simpa only [abs_sub_comm] using hd
    omega
  obtain ⟨u, hu⟩ := int_nonneg_sum_one_single (fun v => max (x v - a v) 0)
    (fun _ => le_max_right _ _) hp
  obtain ⟨v, hv⟩ := int_nonneg_sum_one_single (fun v => max (a v - x v) 0)
    (fun _ => le_max_right _ _) hq
  have hup : 0 < (x - a) u := by
    have h := hu u
    simp only [ite_true] at h
    change 0 < x u - a u
    omega
  have hvn : (x - a) v < 0 := by
    have h := hv v
    simp only [ite_true] at h
    change x v - a v < 0
    omega
  refine ⟨u, v, hup, hvn, ?_⟩
  ext z
  have hpz := hu z
  have hqz := hv z
  simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
  omega

omit [DecidableEq V] in
theorem l1_add_of_between [DecidableEq V] (x a y : V → ℤ)
    (hbox : ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v)) :
    (∑ v, |x v - a v|) + (∑ v, |a v - y v|) = ∑ v, |x v - y v| := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h := hbox v
  by_cases hxy : x v ≤ y v
  · have hxa : x v ≤ a v := by simpa [min_eq_left hxy] using h.1
    have hay : a v ≤ y v := by simpa [max_eq_right hxy] using h.2
    rw [abs_of_nonpos (sub_nonpos.mpr hxa), abs_of_nonpos (sub_nonpos.mpr hay),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    omega
  · have hyx : y v ≤ x v := le_of_lt (lt_of_not_ge hxy)
    have hya : y v ≤ a v := by simpa [min_eq_right hyx] using h.1
    have hax : a v ≤ x v := by simpa [max_eq_left hyx] using h.2
    rw [abs_of_nonneg (sub_nonneg.mpr hax), abs_of_nonneg (sub_nonneg.mpr hya),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    omega

theorem midpoint_exchange_mem_base_checked [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
  classical
  have hsum := base_sum_eq hB hx hy
  have hne : x ≠ y := by intro h; subst y; simp at hxy
  have hpositive : ∃ u, 0 < (x - y) u := by
    by_contra h
    push Not at h
    have hle : ∀ u, x u ≤ y u := by
      intro u
      have h' := h u
      change x u - y u ≤ 0 at h'
      omega
    exact hne (base_eq_of_coordinatewise_le hB hx hy hle)
  have hdirect (hxA : x ∈ A) (hyA : y ∈ A) :
      ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
        x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
    obtain ⟨u, hu⟩ := hpositive
    obtain ⟨v, hv, hxv, hyv⟩ :=
      SteinitzCoordinator.base_symmetric_exchange hA hxA hyA u hu
    exact ⟨u, v, hu, hv, hxv, hyv⟩
  obtain ⟨a, ha, b, hb, hab, hbox⟩ := base_midpoint_complement A hA x y hsum hxy hm
  by_cases hax : a = x
  · subst a
    have hby : b = y := add_left_cancel hab
    exact hdirect ha (hby ▸ hb)
  by_cases hay : a = y
  · subst a
    have hbx : b = x := by
      calc
        b = (y + b) - y := by abel
        _ = (x + y) - y := by rw [hab]
        _ = x := by abel
    exact hdirect (hbx ▸ hb) ha
  have hsa : (∑ v, a v) = ∑ v, x v := by
    have hca := hull_coordinate_sum_eq A hA a ha hm
    have hsumc : (∑ v, ((1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y) v) =
        ((∑ v, x v : ℤ) : ℝ) := by
      simp only [Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hsum]
      ring
    exact_mod_cast hca.symm.trans hsumc
  have hdistadd := l1_add_of_between x a y hbox
  have hpos1 := l1_pos_of_ne x a (Ne.symm hax)
  have hpos2 := l1_pos_of_ne a y hay
  have hpar1 := l1_eq_twice_positiveDeviation x a hsa.symm
  have hpar2 := l1_eq_twice_positiveDeviation a y (hsa.trans hsum)
  have hdist : (∑ v, |x v - a v|) = 2 := by omega
  obtain ⟨u, v, hu, hv, haexpr⟩ := l1_two_unit_exchange x a hsa.symm hdist
  have huy : 0 < (x - y) u := by
    have h := hbox u
    change 0 < x u - a u at hu
    change 0 < x u - y u
    omega
  have hvy : (x - y) v < 0 := by
    have h := hbox v
    change x v - a v < 0 at hv
    change x v - y v < 0
    omega
  have hbexpr : b = y + chi u - chi v := by
    apply add_left_cancel (a := x - chi u + chi v)
    calc
      _ = x + y := by simpa only [haexpr] using hab
      _ = _ := by abel
  exact ⟨u, v, huy, hvy, haexpr ▸ ha, hbexpr ▸ hb⟩


end SteinitzExchange.Extension

open SteinitzExchange.Extension

-- Mission: Convexity and Steinitz's Exchange Property I, Extension Theorem
-- Target: https://prove2.me/theorems/3ac8d0ff-c3a8-4428-b097-3c19f40868c2
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A :=
  midpoint_exchange_mem_base_checked B A hB hA x y hx hy hxy hm


end AttributedSteinitz.Midpoint

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.midpoint_exchange_mem_base {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
  exact AttributedSteinitz.Midpoint.solution B A hB hA x y hx hy hxy hm
end


namespace AttributedSteinitz.ExtensionCharacterization
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet
-- status  : ACCEPTED   (prove)
-- author  : @choi
-- created : 2026-10-01T03:34:37.600658+00:00
-- url     : https://prove2.me/submissions/a972a6c9-3640-4d37-b344-208b4141ef20


open SteinitzExchange.Extension

/-- The maximizer characterization follows from linear perturbation invariance in the forward
 direction and from the midpoint geometry of perturbed maximizer base polytopes in the reverse. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by
  classical
  constructor
  · intro hω p
    exact argmax_isIntegralBaseSet B hB (perturb ω p) (exc_add_linear B hB ω hω p)
  · intro hmax
    apply (exc_iff_exc_loc B hB ω).mpr
    intro x hx y hy hxy
    have hxHull : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x, hx, rfl⟩
    have hyHull : toReal y ∈ hull B := subset_convexHull ℝ _ ⟨y, hy, rfl⟩
    have hmid : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull B :=
      (convex_convexHull ℝ _) hxHull hyHull (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨p, hpmid⟩ := exists_perturb_hull_argmax B hB.1 ω _ hmid
    obtain ⟨u, v, hu, hv, hxu, hyv⟩ := midpoint_exchange_mem_base
      B (argmaxB B (perturb ω p)) hB (hmax p) x y hx hy hxy hpmid
    have hxmem : x - chi u + chi v ∈ B ∧
        ∀ z ∈ B, perturb ω p z ≤ perturb ω p (x - chi u + chi v) :=
      Finset.mem_filter.mp hxu
    have hymem : y + chi u - chi v ∈ B ∧
        ∀ z ∈ B, perturb ω p z ≤ perturb ω p (y + chi u - chi v) :=
      Finset.mem_filter.mp hyv
    refine ⟨u, v, hu, hv, hxmem.1, hymem.1, ?_⟩
    have hsum := add_le_add (hxmem.2 x hx) (hymem.2 y hy)
    dsimp only [perturb] at hsum
    have hpair : pairing p (toReal x) + pairing p (toReal y) =
        pairing p (toReal (x - chi u + chi v)) +
          pairing p (toReal (y + chi u - chi v)) := by
      unfold pairing toReal
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [Pi.sub_apply, Pi.add_apply]
      push_cast
      ring
    linarith only [hsum, hpair]

end AttributedSteinitz.ExtensionCharacterization

section
open SteinitzExchange.Extension
theorem SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by
  exact AttributedSteinitz.ExtensionCharacterization.solution B hB ω
end


namespace AttributedSteinitz.Duality
open _root_.SteinitzExchange.Extension
-- Prove2me | solution 1 for SteinitzExchange.Duality.baseSet_iff_submodular_system
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T19:07:06.61098+00:00
-- url     : https://prove2.me/submissions/639bfae5-0d3e-4541-a6a1-f88c104a062c


/- COMPONENT: Sol_Steinitz_MidpointExchange -/


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem base_eq_of_coordinatewise_le [Fintype V] {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hxy : ∀ w, x w ≤ y w) : x = y := by
  ext u
  by_contra hne
  have hu : 0 < (y - x) u := by
    change 0 < y u - x u
    have := hxy u
    omega
  obtain ⟨v, hv, _⟩ := hB.2 y hy x hx u hu
  change y v - x v < 0 at hv
  have := hxy v
  omega

def positiveDeviation (x y : V → ℤ) : ℤ :=
  ∑ w, max (x w - y w) 0

theorem positiveDeviation_exchange (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    positiveDeviation (x - chi u + chi v) y = positiveDeviation x y - 1 := by
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hpoint : ∀ w, max ((x - chi u + chi v) w - y w) 0 =
      max (x w - y w) 0 - (if w = u then 1 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
        if_neg huv]
      change 0 < x u - y u at hu
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
          if_neg hwu, sub_zero]
        change x v - y v < 0 at hv
        omega
      · simp [Pi.add_apply, Pi.sub_apply, chi, hwu, hwv]
  simp only [positiveDeviation, hpoint, Finset.sum_sub_distrib]
  simp

theorem sum_exchange (x : V → ℤ) (u v : V) :
    (∑ w, (x - chi u + chi v) w) = ∑ w, x w := by
  simp [Pi.add_apply, Pi.sub_apply, chi, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Pi.single_apply]

theorem base_sum_eq {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ w, x w) = ∑ w, y w := by
  classical
  let S := B.filter (fun z => (∑ w, z w) = ∑ w, x w)
  have hS : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image S (fun z => positiveDeviation z y) hS
  have hzB : z ∈ B := (Finset.mem_filter.mp hz).1
  have hzsum : (∑ w, z w) = ∑ w, x w := (Finset.mem_filter.mp hz).2
  have hzle : ∀ u, z u ≤ y u := by
    intro u
    by_contra hnot
    have hu : 0 < (z - y) u := by
      change 0 < z u - y u
      omega
    obtain ⟨v, hv, hz'⟩ := hB.2 z hzB y hy u hu
    have hmem : z - chi u + chi v ∈ S :=
      Finset.mem_filter.mpr ⟨hz', (sum_exchange z u v).trans hzsum⟩
    have hmin' := hmin _ hmem
    rw [positiveDeviation_exchange z y u v hu hv] at hmin'
    omega
  have hzy : z = y := base_eq_of_coordinatewise_le hB hzB hy hzle
  subst z
  exact hzsum.symm


end SteinitzExchange.Extension

set_option autoImplicit false

open Set

namespace SteinitzCoordinator

/-- Symmetric basis exchange, extracted from the existing circuit-cocircuit API.
This is a local draft until its exact-environment compiler check succeeds. -/
theorem symmetric_basis_exchange {α : Type*} (M : Matroid α)
    {X Y : Set α} (hX : M.IsBase X) (hY : M.IsBase Y)
    {e : α} (he : e ∈ X \ Y) :
    ∃ f ∈ Y \ X,
      M.IsBase (insert f (X \ {e})) ∧ M.IsBase (insert e (Y \ {f})) := by
  have heE : e ∈ M.E := hX.subset_ground he.1
  have hC := hY.fundCircuit_isCircuit heE he.2
  have hK := hX.compl_closure_sdiff_singleton_isCocircuit he.1
  have heK : e ∈ M.E \ M.closure (X \ {e}) :=
    ⟨heE, hX.indep.notMem_closure_sdiff_of_mem he.1⟩
  have hn := hC.isCocircuit_inter_nontrivial hK
    ⟨e, M.mem_fundCircuit e Y, heK⟩
  obtain ⟨f, hf, hfe⟩ := hn.exists_ne e
  have hfY : f ∈ Y := by
    have h := M.fundCircuit_subset_insert e Y hf.1
    rcases h with h | h
    · exact (hfe h).elim
    · exact h
  have hfX : f ∉ X := by
    intro h
    exact hf.2.2 (M.subset_closure (X \ {e})
      (sdiff_subset.trans hX.subset_ground) ⟨h, hfe⟩)
  have hecl : e ∈ M.closure Y := by rwa [hY.closure_eq]
  have hi : M.Indep (insert e Y \ {f}) :=
    (hY.indep.mem_fundCircuit_iff hecl he.2).mp hf.1
  refine ⟨f, ⟨hfY, hfX⟩,
    hX.exchange_base_of_notMem_closure he.1 hf.2.2 hf.2.1, ?_⟩
  have hb := hY.exchange_isBase_of_indep' hfY he.2 hi
  simpa only [← insert_sdiff_singleton_comm hfe.symm] using hb


end SteinitzCoordinator

open Set

namespace SteinitzCoordinator

variable {V : Type*} [DecidableEq V]

def cloneFiber (S : Set (V × ℕ)) (i : V) : Set ℕ :=
  {k | (i, k) ∈ S}

noncomputable def cloneCount (S : Set (V × ℕ)) (i : V) : ℤ :=
  (cloneFiber S i).ncard

omit [DecidableEq V] in
lemma cloneFiber_finite [DecidableEq V] {S : Set (V × ℕ)} (hS : S.Finite) (i : V) :
    (cloneFiber S i).Finite := by
  exact hS.preimage (fun _ _ _ _ h => (Prod.mk.inj h).2)

lemma cloneFiber_insert (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (insert (u,k) S) i =
      if i = u then insert k (cloneFiber S i) else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneFiber_delete (S : Set (V × ℕ)) (u i : V) (k : ℕ) :
    cloneFiber (S \ {(u,k)}) i =
      if i = u then cloneFiber S i \ {k} else cloneFiber S i := by
  ext n
  by_cases h : i = u
  · subst i
    simp [cloneFiber]
  · simp [cloneFiber, h]

lemma cloneCount_insert {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∉ S) (i : V) :
    cloneCount (insert (u,k) S) i = cloneCount S i + if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_insert]
  split_ifs with h
  · subst i
    rw [Set.ncard_insert_of_notMem (show k ∉ cloneFiber S u from hk)
      (cloneFiber_finite hS u)]
    simp
  · simp

lemma cloneCount_delete {S : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S) (i : V) :
    cloneCount (S \ {(u,k)}) i = cloneCount S i - if i = u then 1 else 0 := by
  unfold cloneCount
  rw [cloneFiber_delete]
  split_ifs with h
  · subst i
    have hn := Set.ncard_sdiff_singleton_add_one
      (show k ∈ cloneFiber S u from hk) (cloneFiber_finite hS u)
    omega
  · simp

lemma cloneCount_mono {S T : Set (V × ℕ)} (hT : T.Finite)
    (hST : S ⊆ T) (i : V) : cloneCount S i ≤ cloneCount T i := by
  unfold cloneCount
  exact_mod_cast Set.ncard_le_ncard (s := cloneFiber S i) (t := cloneFiber T i)
    (fun k hk => hST hk) (cloneFiber_finite hT i)

lemma exists_clone_difference {S T : Set (V × ℕ)} (hS : S.Finite)
    (i : V) (h : cloneCount S i < cloneCount T i) :
    ∃ k, (i,k) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T i ⊆ cloneFiber S i := by
    intro k hk
    by_contra hkS
    exact hn ⟨k,hk,hkS⟩
  have hc := Set.ncard_le_ncard hsub (cloneFiber_finite hS i)
  unfold cloneCount at h
  omega

lemma exists_clone_same_coordinate {S T : Set (V × ℕ)} (hS : S.Finite)
    (u : V) (k : ℕ) (hk : (u,k) ∈ S \ T)
    (h : cloneCount S u ≤ cloneCount T u) :
    ∃ l, (u,l) ∈ T \ S := by
  by_contra hn
  have hsub : cloneFiber T u ⊆ cloneFiber S u \ {k} := by
    intro l hl
    refine ⟨?_, ?_⟩
    · by_contra hls
      exact hn ⟨l,hl,hls⟩
    · intro hlk
      have heq : l = k := Set.mem_singleton_iff.mp hlk
      change (u,l) ∈ T at hl
      rw [heq] at hl
      exact hk.2 hl
  have hc := Set.ncard_le_ncard hsub ((cloneFiber_finite hS u).sdiff)
  have hd := Set.ncard_sdiff_singleton_add_one
    (show k ∈ cloneFiber S u from hk.1) (cloneFiber_finite hS u)
  unfold cloneCount at h
  omega

lemma cloneCount_swap {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) (i : V) :
    cloneCount (insert (v,l) (S \ {(u,k)})) i =
      cloneCount S i - (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
  rw [cloneCount_insert (hS.sdiff) v l (fun h => hl h.1) i,
    cloneCount_delete hS u k hk i]

variable [Fintype V]

def cloneLift (n : V → ℕ) : Finset (V × ℕ) :=
  Finset.univ.biUnion (fun i => (Finset.range (n i)).image (fun k => (i,k)))

@[simp] lemma mem_cloneLift (n : V → ℕ) (i : V) (k : ℕ) :
    (i,k) ∈ cloneLift n ↔ k < n i := by
  simp [cloneLift, Prod.mk.injEq]

lemma cloneFiber_lift (n : V → ℕ) (i : V) :
    cloneFiber (cloneLift n : Set (V × ℕ)) i = (Finset.range (n i) : Set ℕ) := by
  ext k
  simp [cloneFiber]

@[simp] lemma cloneCount_lift (n : V → ℕ) (i : V) :
    cloneCount (cloneLift n : Set (V × ℕ)) i = n i := by
  unfold cloneCount
  rw [cloneFiber_lift, Set.ncard_coe_finset, Finset.card_range]

end SteinitzCoordinator

open Set
open SteinitzExchange.Extension

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def shiftedCount (m : V → ℤ) (S : Set (V × ℕ)) : V → ℤ :=
  fun i => cloneCount S i + m i

noncomputable def cloneBase (m : V → ℤ) (B : Finset (V → ℤ))
    (S : Set (V × ℕ)) : Prop := S.Finite ∧ shiftedCount m S ∈ B

omit [Fintype V] in
lemma shiftedCount_swap [Fintype V] (m : V → ℤ) {S : Set (V × ℕ)} (hS : S.Finite)
    (u v : V) (k l : ℕ) (hk : (u,k) ∈ S) (hl : (v,l) ∉ S) :
    shiftedCount m (insert (v,l) (S \ {(u,k)})) =
      shiftedCount m S - chi u + chi v := by
  ext i
  simp only [shiftedCount, Pi.add_apply, Pi.sub_apply]
  rw [cloneCount_swap hS u v k l hk hl i]
  simp only [chi, Pi.single_apply]
  split_ifs <;> omega

lemma cloneBase_exchange (m : V → ℤ) {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) : Matroid.ExchangeProperty (cloneBase m B) := by
  intro S T hS hT a ha
  rcases a with ⟨u,k⟩
  by_cases hle : cloneCount S u ≤ cloneCount T u
  · obtain ⟨l, hl⟩ := exists_clone_same_coordinate hS.1 u k ha hle
    refine ⟨(u,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u u k l ha.1 hl.2]
    simpa using hS.2
  · have hu : 0 < (shiftedCount m S - shiftedCount m T) u := by
      simp only [shiftedCount, Pi.sub_apply]
      omega
    obtain ⟨v, hv, hb⟩ := hB.2 _ hS.2 _ hT.2 u hu
    have hlt : cloneCount S v < cloneCount T v := by
      simp only [shiftedCount, Pi.sub_apply] at hv
      omega
    obtain ⟨l, hl⟩ := exists_clone_difference hS.1 v hlt
    refine ⟨(v,l), hl, (hS.1.sdiff).insert _, ?_⟩
    rw [shiftedCount_swap m hS.1 u v k l ha.1 hl.2]
    exact hb

lemma shiftedCount_lift (m x : V → ℤ) (hx : ∀ i, m i ≤ x i) :
    shiftedCount m (cloneLift (fun i => (x i - m i).toNat) : Set (V × ℕ)) = x := by
  ext i
  simp only [shiftedCount, cloneCount_lift]
  have := hx i
  omega

/-- Symmetric exchange for an integral base set with an explicit coordinatewise lower bound.
No new axioms: finite integer vectors are expanded into finite bases on a countable clone ground. -/
theorem base_symmetric_exchange_with_lower_bound
    (m : V → ℤ) {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (hm : ∀ x ∈ B, ∀ i, m i ≤ x i)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let X : Set (V × ℕ) := cloneLift (fun i => (x i - m i).toNat)
  let Y : Set (V × ℕ) := cloneLift (fun i => (y i - m i).toNat)
  have hXfin : X.Finite := Finset.finite_toSet _
  have hYfin : Y.Finite := Finset.finite_toSet _
  have hXcount : shiftedCount m X = x := shiftedCount_lift m x (hm x hx)
  have hYcount : shiftedCount m Y = y := shiftedCount_lift m y (hm y hy)
  have hXB : cloneBase m B X := ⟨hXfin, hXcount.symm ▸ hx⟩
  have hYB : cloneBase m B Y := ⟨hYfin, hYcount.symm ▸ hy⟩
  let M : Matroid (V × ℕ) := Matroid.ofExistsFiniteIsBase Set.univ (cloneBase m B)
    ⟨X, hXB, hXfin⟩ (cloneBase_exchange m hB) (fun _ _ => Set.subset_univ _)
  have hXM : M.IsBase X := hXB
  have hYM : M.IsBase Y := hYB
  let k : ℕ := (y u - m u).toNat
  have hk : (u,k) ∈ X \ Y := by
    have hxu := hm x hx u
    have hyu := hm y hy u
    change 0 < x u - y u at hu
    simp only [X, Y, Set.mem_sdiff, Finset.mem_coe, mem_cloneLift, k]
    omega
  obtain ⟨⟨v,l⟩, hl, hbX, hbY⟩ := symmetric_basis_exchange M hXM hYM hk
  have hv : (x - y) v < 0 := by
    have hxv := hm x hx v
    have hyv := hm y hy v
    simp only [X, Y, Set.mem_sdiff, Finset.mem_coe, mem_cloneLift] at hl
    change x v - y v < 0
    omega
  change cloneBase m B (insert (v,l) (X \ {(u,k)})) at hbX
  change cloneBase m B (insert (u,k) (Y \ {(v,l)})) at hbY
  have hfirst := hbX.2
  have hsecond := hbY.2
  rw [shiftedCount_swap m hXfin u v k l hk.1 hl.2, hXcount] at hfirst
  rw [shiftedCount_swap m hYfin v u l k hl.1 hk.2, hYcount] at hsecond
  refine ⟨v,hv,hfirst,?_⟩
  convert hsecond using 1 ; abel

theorem base_symmetric_exchange {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (u : V) (hu : 0 < (x - y) u) :
    ∃ v : V, (x - y) v < 0 ∧
      x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B := by
  classical
  let m : V → ℤ := fun i => B.inf' hB.1 (fun z => z i)
  apply base_symmetric_exchange_with_lower_bound m hB _ hx hy u hu
  intro z hz i
  exact Finset.inf'_le (fun a => a i) hz


end SteinitzCoordinator


open scoped BigOperators

namespace SteinitzExchange.Extension

section Weights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) : ι → ℝ :=
  fun i => w i - (if i = a then ε else 0) - (if i = b then ε else 0) +
    (if i = a' then ε else 0) + (if i = b' then ε else 0)

omit [Fintype ι] in
theorem transferWeights_nonneg [Fintype ι] (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    ∀ i, 0 ≤ transferWeights w a b a' b' ε i := by
  intro i
  have hp : 0 ≤ (if i = a' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  have hq : 0 ≤ (if i = b' then ε else 0) := by split_ifs <;> first | exact he | exact le_rfl
  unfold transferWeights
  by_cases hia : i = a
  · subst i
    simp only [if_neg hab, ite_true]
    linarith
  · by_cases hib : i = b
    · subst i
      simp only [if_neg hia, ite_true]
      linarith
    · simp only [if_neg hia, if_neg hib]
      have := hw i
      linarith

theorem sum_transferWeights (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i) = ∑ i, w i := by
  simp only [transferWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

theorem weighted_sum_transfer {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ) :
    (∑ i, transferWeights w a b a' b' ε i • p i) =
      (∑ i, w i • p i) - ε • p a - ε • p b + ε • p a' + ε • p b' := by
  simp [transferWeights, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ite_smul]

theorem transferWeights_mem_stdSimplex (w : ι → ℝ) (a b a' b' : ι) (ε : ℝ)
    (hw : w ∈ stdSimplex ℝ ι) (hab : a ≠ b) (he : 0 ≤ ε)
    (hea : ε ≤ w a) (heb : ε ≤ w b) :
    transferWeights w a b a' b' ε ∈ stdSimplex ℝ ι :=
  ⟨transferWeights_nonneg w a b a' b' ε hw.1 hab he hea heb,
    (sum_transferWeights w a b a' b' ε).trans hw.2⟩

theorem barycenter_transfer_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → ℝ) (p : ι → E) (a b a' b' : ι) (ε : ℝ)
    (hp : p a' + p b' = p a + p b) :
    (∑ i, transferWeights w a b a' b' ε i • p i) = ∑ i, w i • p i := by
  rw [weighted_sum_transfer]
  have heq := congrArg (fun z => ε • z) hp
  simp only [smul_add] at heq
  calc
    _ = (∑ i, w i • p i) - (ε • p a + ε • p b) +
        (ε • p a' + ε • p b') := by abel
    _ = _ := by rw [heq]; exact sub_add_cancel _ _

end Weights

section Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

def integerEnergy (x : V → ℤ) : ℤ := ∑ w, (x w) ^ 2

theorem integerEnergy_exchange (a b : V → ℤ) (u v : V) (huv : u ≠ v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) -
      integerEnergy a - integerEnergy b =
        -2 * (a u - b u) + 2 * (a v - b v) + 4 := by
  have hpoint : ∀ w,
      ((a - chi u + chi v) w) ^ 2 + ((b + chi u - chi v) w) ^ 2 -
          (a w) ^ 2 - (b w) ^ 2 =
        (if w = u then -2 * (a u - b u) + 2 else 0) +
        (if w = v then 2 * (a v - b v) + 2 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp [chi, huv] ; ring
    · by_cases hwv : w = v
      · subst w
        simp [chi, hwu] ; ring
      · simp [chi, hwu, hwv]
  unfold integerEnergy
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp ; ring

theorem integerEnergy_exchange_lt (a b : V → ℤ) (u v : V)
    (hu : b u + 2 ≤ a u) (hv : a v < b v) :
    integerEnergy (a - chi u + chi v) + integerEnergy (b + chi u - chi v) <
      integerEnergy a + integerEnergy b := by
  have huv : u ≠ v := by intro h; subst v; omega
  have he := integerEnergy_exchange a b u v huv
  omega

end Energy

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

section ConvexWeights

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]

theorem convexHull_range_exists_weights (p : ι → E) {c : E}
    (hc : c ∈ convexHull ℝ (Set.range p)) :
    ∃ w : ι → ℝ, w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = c := by
  have hconv : Convex ℝ {z : E | ∃ w : ι → ℝ,
      w ∈ stdSimplex ℝ ι ∧ ∑ i, w i • p i = z} := by
    rintro x ⟨w, hw, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
    refine ⟨a • w + b • v, (convex_stdSimplex ℝ ι) hw hv ha hb hab, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      Finset.sum_add_distrib, ← Finset.smul_sum]
  apply convexHull_min ?_ hconv hc
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
  simp [Pi.single_apply, ite_smul]

end ConvexWeights

section BaseWeights

variable {V : Type*} [Fintype V] [DecidableEq V]

def baseBarycenter (A : Finset (V → ℤ)) (w : A → ℝ) : V → ℝ :=
  ∑ a : A, w a • toReal a.1

def weightedEnergy (A : Finset (V → ℤ)) (w : A → ℝ) : ℝ :=
  ∑ a : A, w a * (integerEnergy a.1 : ℝ)

omit [DecidableEq V] in
theorem hull_exists_weights [DecidableEq V] (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c := by
  have hr : Set.range (fun a : A => toReal a.1) =
      toReal '' (A : Set (V → ℤ)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  apply convexHull_range_exists_weights (fun a : A => toReal a.1)
  simpa only [hr, hull] using hc

theorem hull_coordinate_sum_eq (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (a : V → ℤ) (ha : a ∈ A) {c : V → ℝ} (hc : c ∈ hull A) :
    (∑ v, c v) = ((∑ v, a v : ℤ) : ℝ) := by
  obtain ⟨w, hw, hbar⟩ := hull_exists_weights A hc
  rw [← hbar]
  simp only [baseBarycenter, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← Int.cast_sum]
  have hs : ∀ b : A, (∑ v, b.1 v) = ∑ v, a v :=
    fun b => base_sum_eq hA b.2 ha
  simp_rw [hs]
  rw [← Finset.sum_mul, hw.2, one_mul]

theorem exists_minimal_energy_weights (A : Finset (V → ℤ)) {c : V → ℝ}
    (hc : c ∈ hull A) :
    ∃ w : A → ℝ, w ∈ stdSimplex ℝ A ∧ baseBarycenter A w = c ∧
      ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
        weightedEnergy A w ≤ weightedEnergy A v := by
  let K : Set (A → ℝ) := stdSimplex ℝ A ∩ {w | baseBarycenter A w = c}
  have hbar : Continuous (baseBarycenter A) := by unfold baseBarycenter; fun_prop
  have henergy : Continuous (weightedEnergy A) := by unfold weightedEnergy; fun_prop
  have hcompact : IsCompact K :=
    (isCompact_stdSimplex ℝ A).inter_right (isClosed_eq hbar continuous_const)
  obtain ⟨w, hw, hbarw⟩ := hull_exists_weights A hc
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn ⟨w, hw, hbarw⟩ henergy.continuousOn
  exact ⟨v, hv.1, hv.2, fun z hz hbarz => hmin ⟨hz, hbarz⟩⟩

def SymmetricBaseExchange (A : Finset (V → ℤ)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ u : V, b u < a u →
    ∃ v : V, a v < b v ∧ a - chi u + chi v ∈ A ∧ b + chi u - chi v ∈ A

theorem minimal_energy_support_close (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (w : A → ℝ)
    (hw : w ∈ stdSimplex ℝ A) (hbar : baseBarycenter A w = c)
    (hmin : ∀ v : A → ℝ, v ∈ stdSimplex ℝ A → baseBarycenter A v = c →
      weightedEnergy A w ≤ weightedEnergy A v) :
    ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1 := by
  classical
  intro a b ha hb u
  by_contra hnot
  have hu : b.1 u + 2 ≤ a.1 u := by omega
  obtain ⟨v, hv, ha', hb'⟩ := hA a.1 a.2 b.1 b.2 u (by omega)
  let a' : A := ⟨a.1 - chi u + chi v, ha'⟩
  let b' : A := ⟨b.1 + chi u - chi v, hb'⟩
  let ε := min (w a) (w b)
  have he : 0 < ε := lt_min ha hb
  have hab : a ≠ b := by intro h; subst b; omega
  let w' := transferWeights w a b a' b' ε
  have hw' : w' ∈ stdSimplex ℝ A :=
    transferWeights_mem_stdSimplex w a b a' b' ε hw hab (le_of_lt he)
      (min_le_left _ _) (min_le_right _ _)
  have hp : toReal a'.1 + toReal b'.1 = toReal a.1 + toReal b.1 := by
    ext z
    simp [a', b', toReal]
  have hbar' : baseBarycenter A w' = c := by
    change (∑ i : A, transferWeights w a b a' b' ε i • toReal i.1) = c
    rw [barycenter_transfer_eq w (fun i : A => toReal i.1) a b a' b' ε hp]
    exact hbar
  have henergy : (integerEnergy a'.1 : ℝ) + integerEnergy b'.1 <
      integerEnergy a.1 + integerEnergy b.1 := by
    exact_mod_cast integerEnergy_exchange_lt a.1 b.1 u v hu hv
  have hdrop := mul_lt_mul_of_pos_left henergy he
  have htransfer : weightedEnergy A w' = weightedEnergy A w -
      ε * integerEnergy a.1 - ε * integerEnergy b.1 +
      ε * integerEnergy a'.1 + ε * integerEnergy b'.1 := by
    simpa only [weightedEnergy, w', smul_eq_mul] using
      weighted_sum_transfer w (fun i : A => (integerEnergy i.1 : ℝ)) a b a' b' ε
  have hcontr := hmin w' hw' hbar'
  rw [htransfer] at hcontr
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem balanced_support_mem_integer_box [Fintype V] [DecidableEq V] (A : Finset (V → ℤ))
    {c : V → ℝ} (w : A → ℝ) (hw : w ∈ stdSimplex ℝ A)
    (hbar : baseBarycenter A w = c)
    (hclose : ∀ a b : A, 0 < w a → 0 < w b → ∀ u, a.1 u ≤ b.1 u + 1)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    ∀ a : A, 0 < w a → ∀ u, lo u ≤ a.1 u ∧ a.1 u ≤ hi u := by
  classical
  intro a ha u
  have hcoord : (∑ b : A, w b * (b.1 u : ℝ)) = c u := by
    simpa [baseBarycenter, toReal, Finset.sum_apply] using congrFun hbar u
  constructor
  · by_contra hnot
    have hal : a.1 u < lo u := by omega
    have hle : ∀ b : A, w b * (b.1 u : ℝ) ≤ w b * (lo u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : b.1 u ≤ lo u := by have := hclose b a hb ha u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (b.1 u : ℝ)) < ∑ b : A, w b * (lo u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hal) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hlo u)) hlt
  · by_contra hnot
    have hai : hi u < a.1 u := by omega
    have hle : ∀ b : A, w b * (hi u : ℝ) ≤ w b * (b.1 u : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : hi u ≤ b.1 u := by have := hclose a b ha hb u; omega
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbi) (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hlt : (∑ b : A, w b * (hi u : ℝ)) < ∑ b : A, w b * (b.1 u : ℝ) :=
      Finset.sum_lt_sum (fun b _ => hle b)
        ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (by exact_mod_cast hai) ha⟩
    rw [hcoord, ← Finset.sum_mul, hw.2, one_mul] at hlt
    exact (not_lt_of_ge (hhi u)) hlt

theorem symmetricBaseExchange_hull_box (A : Finset (V → ℤ))
    (hA : SymmetricBaseExchange A) {c : V → ℝ} (hc : c ∈ hull A)
    (lo hi : V → ℤ) (hlo : ∀ u, (lo u : ℝ) ≤ c u)
    (hhi : ∀ u, c u ≤ (hi u : ℝ)) :
    c ∈ hull (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u)) := by
  classical
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hc
  have hclose := minimal_energy_support_close A hA w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    have hnonpos : w a ≤ 0 := le_of_not_gt (by simpa [t] using hnot)
    exact le_antisymm hnonpos (hw.1 a)
  have hsum : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  have hbar' : ∑ a ∈ t, w a • toReal a.1 = c := by
    rw [← hbar]
    unfold baseBarycenter
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    simp [hout a hnot]
  have hmem : t.centerMass w (fun a : A => toReal a.1) ∈
      convexHull ℝ (toReal '' (A.filter (fun a => ∀ u, lo u ≤ a u ∧ a u ≤ hi u) :
        Set (V → ℤ))) := by
    apply t.centerMass_mem_convexHull (fun a _ => hw.1 a) (by rw [hsum]; norm_num)
    intro a ha
    exact ⟨a.1, Finset.mem_filter.mpr ⟨a.2, hbox a (by simpa [t] using ha)⟩, rfl⟩
  rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, hbar'] at hmem
  exact hmem


end BaseWeights

end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

omit [DecidableEq V] in
theorem binary_complement_of_overlap_zero [DecidableEq V] (r a b : V → ℤ)
    (_hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (ha : ∀ v, 0 ≤ a v ∧ a v ≤ r v)
    (hb : ∀ v, 0 ≤ b v ∧ b v ≤ r v)
    (hsum : (∑ v, a v) + (∑ v, b v) = ∑ v, r v)
    (hoverlap : (∑ v, a v * b v) = 0) :
    ∀ v, a v + b v = r v := by
  have hprod : ∀ v, a v * b v = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (ha v).1 (hb v).1)).mp hoverlap
    exact fun v => h v (Finset.mem_univ v)
  have hle : ∀ v, a v + b v ≤ r v := by
    intro v
    rcases mul_eq_zero.mp (hprod v) with h | h <;>
      have := ha v <;> have := hb v <;> omega
  have heq : (∑ v, (a v + b v)) = ∑ v, r v := by
    rw [Finset.sum_add_distrib]
    exact hsum
  have h := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp heq
  exact fun v => h v (Finset.mem_univ v)

omit [DecidableEq ι] in
/-- Rank at most two: half marginals force complementary support vectors. -/
theorem binary_half_marginals_complement [DecidableEq ι] (r : V → ℤ) (p : ι → V → ℤ)
    (k : ℤ) (hk : k ≤ 2)
    (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (hp : ∀ i v, 0 ≤ p i v ∧ p i v ≤ r v)
    (hsum : ∀ i, (∑ v, p i v) = k)
    (hrsum : (∑ v, r v) = 2 * k)
    (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι)
    (hmean : ∀ v, (∑ i, w i * (p i v : ℝ)) = (r v : ℝ) / 2) :
    ∃ a b : ι, 0 < w a ∧ 0 < w b ∧ ∀ v, p a v + p b v = r v := by
  classical
  have haex : ∃ a, 0 < w a := by
    by_contra h
    push Not at h
    have hnonpos : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    rw [hw.2] at hnonpos
    norm_num at hnonpos
  obtain ⟨a, ha⟩ := haex
  let overlap : ι → ℤ := fun b => ∑ v, p a v * p b v
  have hoverlap_nonneg : ∀ b, 0 ≤ overlap b :=
    fun b => Finset.sum_nonneg (fun v _ => mul_nonneg (hp a v).1 (hp b v).1)
  have har : ∀ v, p a v * r v = p a v := by
    intro v
    have hrv := hr v
    have hav := hp a v
    have hcases : r v = 0 ∨ r v = 1 := by omega
    rcases hcases with h | h
    · have hpa : p a v = 0 := by omega
      simp [hpa]
    · simp [h]
  have hself : overlap a = k := by
    change (∑ v, p a v * p a v) = k
    rw [← hsum a]
    apply Finset.sum_congr rfl
    intro v _
    have hrv := hr v
    have hav := hp a v
    have hcases : p a v = 0 ∨ p a v = 1 := by omega
    rcases hcases with h | h <;> simp [h]
  have hmean_overlap : (∑ b, w b * (overlap b : ℝ)) = (k : ℝ) / 2 := by
    calc
      _ = ∑ v, (p a v : ℝ) * (∑ b, w b * (p b v : ℝ)) := by
        simp only [overlap, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ v, (p a v : ℝ) * ((r v : ℝ) / 2) := by simp_rw [hmean]
      _ = (∑ v, (p a v : ℝ)) / 2 := by
        simp_rw [← mul_div_assoc, ← Int.cast_mul, har]
        simp only [div_eq_mul_inv, Finset.sum_mul]
      _ = (k : ℝ) / 2 := by rw [← Int.cast_sum, hsum a]
  have hbex : ∃ b, 0 < w b ∧ overlap b = 0 := by
    by_contra h
    push Not at h
    have hle : ∀ b, w b ≤ w b * (overlap b : ℝ) := by
      intro b
      by_cases hb : 0 < w b
      · have hbi : (1 : ℤ) ≤ overlap b := by
          have := hoverlap_nonneg b
          have := h b hb
          omega
        have hbr : (1 : ℝ) ≤ overlap b := by exact_mod_cast hbi
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hbr (hw.1 b)
      · have hb0 : w b = 0 := le_antisymm (le_of_not_gt hb) (hw.1 b)
        simp [hb0]
    have hsum_le := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hle b)
    rw [hw.2, hmean_overlap] at hsum_le
    have hkreal : (2 : ℝ) ≤ k := by linarith
    have hkint : (2 : ℤ) ≤ k := by exact_mod_cast hkreal
    have hk2 : k = 2 := le_antisymm hk hkint
    have hlt : (∑ b, w b) < ∑ b, w b * (overlap b : ℝ) := by
      apply Finset.sum_lt_sum (fun b _ => hle b)
      refine ⟨a, Finset.mem_univ a, ?_⟩
      rw [hself, hk2]
      norm_num
      linarith
    rw [hw.2, hmean_overlap, hk2] at hlt
    norm_num at hlt
  obtain ⟨b, hb, hab⟩ := hbex
  refine ⟨a, b, ha, hb, binary_complement_of_overlap_zero r (p a) (p b)
    hr (hp a) (hp b) ?_ hab⟩
  rw [hsum a, hsum b, hrsum]
  omega


end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem integralBase_symmetric (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A) :
    SymmetricBaseExchange A := by
  intro a ha b hb u hu
  obtain ⟨v, hv, hav, hbv⟩ := SteinitzCoordinator.base_symmetric_exchange hA ha hb u
    (by simpa only [Pi.sub_apply, sub_pos] using hu)
  exact ⟨v, by simpa only [Pi.sub_apply, sub_neg] using hv, hav, hbv⟩

theorem toReal_mem_hull_iff_checked (A : Finset (V → ℤ))
    (hA : IsIntegralBaseSet A) (x : V → ℤ) : toReal x ∈ hull A ↔ x ∈ A := by
  classical
  constructor
  · intro hx
    have hb := symmetricBaseExchange_hull_box A (integralBase_symmetric A hA) hx x x
      (fun _ => le_rfl) (fun _ => le_rfl)
    have hn : (toReal '' (A.filter (fun a => ∀ u, x u ≤ a u ∧ a u ≤ x u) :
        Set (V → ℤ))).Nonempty := (convexHull_nonempty_iff).mp ⟨toReal x, hb⟩
    rcases hn with ⟨z, a, ha, _⟩
    obtain ⟨haA, hax⟩ := Finset.mem_filter.mp ha
    have he : a = x := funext (fun u => le_antisymm (hax u).2 (hax u).1)
    exact he ▸ haA
  · intro hx
    exact subset_convexHull ℝ _ ⟨x, hx, rfl⟩


/-- The substantial convex-geometric core: a midpoint at lattice distance four
has a complementary pair in the integral base set containing that midpoint. -/
theorem base_midpoint_complement (A : Finset (V → ℤ)) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hxySum : (∑ v, x v) = ∑ v, y v)
    (hxy : (∑ v, |x v - y v|) = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ a ∈ A, ∃ b ∈ A, a + b = x + y ∧
      ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v) := by
  classical
  let c : V → ℝ := (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y
  let lo : V → ℤ := fun v => (x v + y v) / 2
  let hi : V → ℤ := fun v => x v + y v - lo v
  let r : V → ℤ := fun v => x v + y v - 2 * lo v
  let k : ℤ := (∑ v, x v) - ∑ v, lo v
  have hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1 := by
    intro v
    dsimp [r, lo]
    omega
  have hlo : ∀ v, (lo v : ℝ) ≤ c v := by
    intro v
    have hdiv : 2 * lo v ≤ x v + y v := by dsimp [lo]; omega
    have hdivR : 2 * (lo v : ℝ) ≤ (x v : ℝ) + y v := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hhi : ∀ v, c v ≤ (hi v : ℝ) := by
    intro v
    have hdiv : x v + y v ≤ 2 * hi v := by dsimp [hi, lo]; omega
    have hdivR : (x v : ℝ) + y v ≤ 2 * (hi v : ℝ) := by exact_mod_cast hdiv
    dsimp [c, toReal]
    linarith
  have hsumc : (∑ v, c v) = ((∑ v, x v : ℤ) : ℝ) := by
    simp only [c, Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hxySum]
    ring
  have hsumA : ∀ a : A, (∑ v, a.1 v) = ∑ v, x v := by
    intro a
    have he := (hull_coordinate_sum_eq A hA a.1 a.2 hm).symm.trans hsumc
    exact_mod_cast he
  have hrsum : (∑ v, r v) = 2 * k := by
    simp only [r, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← hxySum, k]
    ring
  have hrle : ∀ v, r v ≤ |x v - y v| := by
    intro v
    by_cases he : x v = y v
    · dsimp [r, lo]
      rw [he]
      simp only [sub_self, abs_zero]
      omega
    · have habs : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr he)
      have := hr v
      omega
  have hk : k ≤ 2 := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hrle v)
    rw [hrsum, hxy] at h
    omega
  obtain ⟨w, hw, hbar, hmin⟩ := exists_minimal_energy_weights A hm
  have hclose := minimal_energy_support_close A (integralBase_symmetric A hA) w hw hbar hmin
  have hbox := balanced_support_mem_integer_box A w hw hbar hclose lo hi hlo hhi
  let t := Finset.univ.filter (fun a : A => 0 < w a)
  have hpos : ∀ a : t, 0 < w a.1 := by intro a; simpa [t] using a.2
  have hout : ∀ a : A, a ∉ t → w a = 0 := by
    intro a hnot
    exact le_antisymm (le_of_not_gt (by simpa [t] using hnot)) (hw.1 a)
  have hsumt : ∑ a ∈ t, w a = 1 := by
    rw [← hw.2]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ hnot
    exact hout a hnot
  let wt : t → ℝ := fun a => w a.1
  let p : t → V → ℤ := fun a v => a.1.1 v - lo v
  have hwt : wt ∈ stdSimplex ℝ t :=
    ⟨fun a => hw.1 a.1, by simpa only [wt, Finset.sum_coe_sort] using hsumt⟩
  have hp : ∀ a v, 0 ≤ p a v ∧ p a v ≤ r v := by
    intro a v
    have h := hbox a.1 (hpos a) v
    dsimp [p, hi, r] at *
    omega
  have hpsum : ∀ a, (∑ v, p a v) = k := by
    intro a
    simp only [p, Finset.sum_sub_distrib, hsumA, k]
  have hmean : ∀ v, (∑ a, wt a * (p a v : ℝ)) = (r v : ℝ) / 2 := by
    intro v
    have hcoord : (∑ a : A, w a * (a.1 v : ℝ)) = c v := by
      simpa [baseBarycenter, toReal, Finset.sum_apply, c] using congrFun hbar v
    have hcoordt : (∑ a ∈ t, w a * (a.1 v : ℝ)) = c v := by
      rw [← hcoord]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a _ hnot
      simp [hout a hnot]
    have hcoordt' : (∑ a : t, wt a * (a.1.1 v : ℝ)) = c v := by
      change (∑ a : t, w a.1 * (a.1.1 v : ℝ)) = c v
      exact (Finset.sum_coe_sort t (fun a : A => w a * (a.1 v : ℝ))).trans hcoordt
    calc
      _ = (∑ a : t, wt a * (a.1.1 v : ℝ)) - (∑ a : t, wt a) * (lo v : ℝ) := by
        simp [p, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = c v - (lo v : ℝ) := by rw [hcoordt', hwt.2, one_mul]
      _ = (r v : ℝ) / 2 := by simp [c, r, toReal]; ring
  obtain ⟨a, b, ha, hb, hab⟩ :=
    binary_half_marginals_complement r p k hk hr hp hpsum hrsum wt hwt hmean
  refine ⟨a.1.1, a.1.2, b.1.1, b.1.2, ?_, ?_⟩
  · ext v
    have h := hab v
    dsimp [p, r] at h
    change a.1.1 v + b.1.1 v = x v + y v
    omega
  · intro v
    have h := hbox a.1 (hpos a) v
    have hlow : min (x v) (y v) ≤ lo v := by dsimp [lo]; omega
    have hhigh : hi v ≤ max (x v) (y v) := by dsimp [hi, lo]; omega
    exact ⟨hlow.trans h.1, h.2.trans hhigh⟩


end SteinitzExchange.Extension


open scoped BigOperators

namespace SteinitzExchange.Extension

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem int_nonneg_sum_one_single (p : V → ℤ) (hp : ∀ v, 0 ≤ p v)
    (hs : (∑ v, p v) = 1) : ∃ u, ∀ v, p v = if v = u then 1 else 0 := by
  classical
  have hex : ∃ u, 0 < p u := by
    by_contra h
    push Not at h
    have hz : ∀ v, p v = 0 := fun v => le_antisymm (h v) (hp v)
    simp [hz] at hs
  obtain ⟨u, hu⟩ := hex
  have hle : p u ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun v _ => hp v) (Finset.mem_univ u)
  have hpu : p u = 1 := by omega
  have herase : (∑ v ∈ Finset.univ.erase u, p v) = 0 := by
    have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ u)
    rw [hs, hpu] at h
    omega
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ Finset.univ.erase u) => hp v)).mp herase
  refine ⟨u, fun v => ?_⟩
  by_cases hv : v = u
  · subst v
    simp [hpu]
  · simp [hv, hz v (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩)]

omit [DecidableEq V] in
theorem l1_eq_twice_positiveDeviation [DecidableEq V] (x y : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, y v) :
    (∑ v, |x v - y v|) = 2 * positiveDeviation x y := by
  have hpoint : ∀ v, |x v - y v| = 2 * max (x v - y v) 0 - (x v - y v) := by
    intro v
    by_cases h : 0 ≤ x v - y v
    · rw [abs_of_nonneg h, max_eq_left h]
      omega
    · have h' : x v - y v ≤ 0 := le_of_lt (lt_of_not_ge h)
      rw [abs_of_nonpos h', max_eq_right h']
      omega
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs,
    sub_self, sub_zero]
  rfl

omit [DecidableEq V] in
theorem l1_pos_of_ne [DecidableEq V] (x y : V → ℤ) (hne : x ≠ y) : 0 < ∑ v, |x v - y v| := by
  have hex : ∃ v, x v ≠ y v := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨v, hv⟩ := hex
  have hpos : 0 < |x v - y v| := abs_pos.mpr (sub_ne_zero.mpr hv)
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (fun w _ => abs_nonneg (x w - y w)) (Finset.mem_univ v))

theorem l1_two_unit_exchange (x a : V → ℤ)
    (hs : (∑ v, x v) = ∑ v, a v) (hd : (∑ v, |x v - a v|) = 2) :
    ∃ u v, 0 < (x - a) u ∧ (x - a) v < 0 ∧ a = x - chi u + chi v := by
  have hp : positiveDeviation x a = 1 := by
    have h := l1_eq_twice_positiveDeviation x a hs
    omega
  have hq : positiveDeviation a x = 1 := by
    have h := l1_eq_twice_positiveDeviation a x hs.symm
    have hd' : (∑ v, |a v - x v|) = 2 := by simpa only [abs_sub_comm] using hd
    omega
  obtain ⟨u, hu⟩ := int_nonneg_sum_one_single (fun v => max (x v - a v) 0)
    (fun _ => le_max_right _ _) hp
  obtain ⟨v, hv⟩ := int_nonneg_sum_one_single (fun v => max (a v - x v) 0)
    (fun _ => le_max_right _ _) hq
  have hup : 0 < (x - a) u := by
    have h := hu u
    simp only [ite_true] at h
    change 0 < x u - a u
    omega
  have hvn : (x - a) v < 0 := by
    have h := hv v
    simp only [ite_true] at h
    change x v - a v < 0
    omega
  refine ⟨u, v, hup, hvn, ?_⟩
  ext z
  have hpz := hu z
  have hqz := hv z
  simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
  omega

omit [DecidableEq V] in
theorem l1_add_of_between [DecidableEq V] (x a y : V → ℤ)
    (hbox : ∀ v, min (x v) (y v) ≤ a v ∧ a v ≤ max (x v) (y v)) :
    (∑ v, |x v - a v|) + (∑ v, |a v - y v|) = ∑ v, |x v - y v| := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have h := hbox v
  by_cases hxy : x v ≤ y v
  · have hxa : x v ≤ a v := by simpa [min_eq_left hxy] using h.1
    have hay : a v ≤ y v := by simpa [max_eq_right hxy] using h.2
    rw [abs_of_nonpos (sub_nonpos.mpr hxa), abs_of_nonpos (sub_nonpos.mpr hay),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    omega
  · have hyx : y v ≤ x v := le_of_lt (lt_of_not_ge hxy)
    have hya : y v ≤ a v := by simpa [min_eq_right hyx] using h.1
    have hax : a v ≤ x v := by simpa [max_eq_left hyx] using h.2
    rw [abs_of_nonneg (sub_nonneg.mpr hax), abs_of_nonneg (sub_nonneg.mpr hya),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    omega

theorem midpoint_exchange_mem_base_checked [Nonempty V]
    (B A : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (hA : IsIntegralBaseSet A)
    (x y : V → ℤ) (hx : x ∈ B) (hy : y ∈ B) (hxy : ∑ w, |x w - y w| = 4)
    (hm : (1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y ∈ hull A) :
    ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
      x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
  classical
  have hsum := base_sum_eq hB hx hy
  have hne : x ≠ y := by intro h; subst y; simp at hxy
  have hpositive : ∃ u, 0 < (x - y) u := by
    by_contra h
    push Not at h
    have hle : ∀ u, x u ≤ y u := by
      intro u
      have h' := h u
      change x u - y u ≤ 0 at h'
      omega
    exact hne (base_eq_of_coordinatewise_le hB hx hy hle)
  have hdirect (hxA : x ∈ A) (hyA : y ∈ A) :
      ∃ u v : V, 0 < (x - y) u ∧ (x - y) v < 0 ∧
        x - chi u + chi v ∈ A ∧ y + chi u - chi v ∈ A := by
    obtain ⟨u, hu⟩ := hpositive
    obtain ⟨v, hv, hxv, hyv⟩ :=
      SteinitzCoordinator.base_symmetric_exchange hA hxA hyA u hu
    exact ⟨u, v, hu, hv, hxv, hyv⟩
  obtain ⟨a, ha, b, hb, hab, hbox⟩ := base_midpoint_complement A hA x y hsum hxy hm
  by_cases hax : a = x
  · subst a
    have hby : b = y := add_left_cancel hab
    exact hdirect ha (hby ▸ hb)
  by_cases hay : a = y
  · subst a
    have hbx : b = x := by
      calc
        b = (y + b) - y := by abel
        _ = (x + y) - y := by rw [hab]
        _ = x := by abel
    exact hdirect (hbx ▸ hb) ha
  have hsa : (∑ v, a v) = ∑ v, x v := by
    have hca := hull_coordinate_sum_eq A hA a ha hm
    have hsumc : (∑ v, ((1 / 2 : ℝ) • toReal x + (1 / 2 : ℝ) • toReal y) v) =
        ((∑ v, x v : ℤ) : ℝ) := by
      simp only [Pi.add_apply, Pi.smul_apply, toReal, smul_eq_mul,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Int.cast_sum, ← hsum]
      ring
    exact_mod_cast hca.symm.trans hsumc
  have hdistadd := l1_add_of_between x a y hbox
  have hpos1 := l1_pos_of_ne x a (Ne.symm hax)
  have hpos2 := l1_pos_of_ne a y hay
  have hpar1 := l1_eq_twice_positiveDeviation x a hsa.symm
  have hpar2 := l1_eq_twice_positiveDeviation a y (hsa.trans hsum)
  have hdist : (∑ v, |x v - a v|) = 2 := by omega
  obtain ⟨u, v, hu, hv, haexpr⟩ := l1_two_unit_exchange x a hsa.symm hdist
  have huy : 0 < (x - y) u := by
    have h := hbox u
    change 0 < x u - a u at hu
    change 0 < x u - y u
    omega
  have hvy : (x - y) v < 0 := by
    have h := hbox v
    change x v - a v < 0 at hv
    change x v - y v < 0
    omega
  have hbexpr : b = y + chi u - chi v := by
    apply add_left_cancel (a := x - chi u + chi v)
    calc
      _ = x + y := by simpa only [haexpr] using hab
      _ = _ := by abel
  exact ⟨u, v, huy, hvy, haexpr ▸ ha, hbexpr ▸ hb⟩


end SteinitzExchange.Extension

open SteinitzExchange.Extension

-- Mission: Convexity and Steinitz's Exchange Property I, Extension Theorem
-- Target: https://prove2.me/theorems/3ac8d0ff-c3a8-4428-b097-3c19f40868c2

/- COMPONENT: CoordinatorForward -/
set_option autoImplicit false

open scoped BigOperators
open SteinitzExchange.Extension

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [DecidableEq V]

def coordSum (S : Finset V) (x : V → ℤ) : ℤ := ∑ i ∈ S, x i

omit [Fintype V] in
lemma coordSum_exchange [Fintype V] (S : Finset V) (x : V → ℤ) (u v : V) :
    coordSum S (x - chi u + chi v) =
      coordSum S x - (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  simp [coordSum, Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma exists_surplus_outside {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) (U : Finset V)
    (hlt : coordSum U x < coordSum U y) :
    ∃ i, i ∉ U ∧ 0 < (x-y) i := by
  by_contra hn
  have hcomp : (∑ i ∈ Uᶜ, x i) ≤ ∑ i ∈ Uᶜ, y i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiU : i ∉ U := Finset.mem_compl.mp hi
    by_contra hnot
    apply hn
    refine ⟨i,hiU,?_⟩
    change 0 < x i - y i
    omega
  have ht := base_sum_eq hB hx hy
  have hcx := Finset.sum_add_sum_compl U (fun i => x i)
  have hcy := Finset.sum_add_sum_compl U (fun i => y i)
  unfold coordSum at hlt
  omega

/-- A finite base set has a point simultaneously maximizing any two nested sums. -/
theorem nested_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (T U : Finset V) (hTU : T ⊆ U) :
    ∃ x ∈ B, (∀ z ∈ B, coordSum T z ≤ coordSum T x) ∧
      (∀ z ∈ B, coordSum U z ≤ coordSum U x) := by
  classical
  obtain ⟨z,hz,hzmax⟩ := Finset.exists_max_image B (coordSum T) hB.1
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image B (coordSum U) hB.1
  let S := B.filter (fun x => coordSum T x = coordSum T z)
  have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,rfl⟩⟩
  obtain ⟨x,hxS,hmin⟩ := Finset.exists_min_image S
    (fun x => positiveDeviation x y) hS
  have hx : x ∈ B := (Finset.mem_filter.mp hxS).1
  have hxT : coordSum T x = coordSum T z := (Finset.mem_filter.mp hxS).2
  have hmaxT : ∀ a ∈ B, coordSum T a ≤ coordSum T x := by
    intro a ha
    rw [hxT]
    exact hzmax a ha
  have hxU : coordSum U x = coordSum U y := by
    by_contra hne
    have hlt : coordSum U x < coordSum U y := by
      have := hymax x hx
      omega
    obtain ⟨u,huU,hu⟩ := exists_surplus_outside hB hx hy U hlt
    obtain ⟨v,hv,hx'⟩ := hB.2 x hx y hy u hu
    have huT : u ∉ T := fun h => huU (hTU h)
    have hvT : v ∉ T := by
      intro hvT
      have hh := hmaxT (x-chi u+chi v) hx'
      rw [coordSum_exchange,if_neg huT,if_pos hvT] at hh
      omega
    have heq : coordSum T (x-chi u+chi v) = coordSum T z := by
      rw [coordSum_exchange,if_neg huT,if_neg hvT]
      simpa using hxT
    have hmem : x-chi u+chi v ∈ S := Finset.mem_filter.mpr ⟨hx',heq⟩
    have hm := hmin _ hmem
    rw [positiveDeviation_exchange x y u v hu hv] at hm
    omega
  refine ⟨x,hx,hmaxT,?_⟩
  intro a ha
  rw [hxU]
  exact hymax a ha

/-- Extend a previously feasible family of tight maxima by a containing set. -/
theorem extend_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V)) (U : Finset V) (hCU : ∀ T ∈ C, T ⊆ U)
    (hprior : ∃ z ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T z) :
    ∃ x ∈ B, (∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x) ∧
      (∀ a ∈ B, coordSum U a ≤ coordSum U x) := by
  classical
  obtain ⟨z,hz,hzmax⟩ := hprior
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image B (coordSum U) hB.1
  let S := B.filter (fun x => ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x)
  have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,hzmax⟩⟩
  obtain ⟨x,hxS,hmin⟩ := Finset.exists_min_image S
    (fun x => positiveDeviation x y) hS
  have hx : x ∈ B := (Finset.mem_filter.mp hxS).1
  have hxmax := (Finset.mem_filter.mp hxS).2
  have hxU : coordSum U x = coordSum U y := by
    by_contra hne
    have hlt : coordSum U x < coordSum U y := by
      have := hymax x hx
      omega
    obtain ⟨u,huU,hu⟩ := exists_surplus_outside hB hx hy U hlt
    obtain ⟨v,hv,hx'⟩ := hB.2 x hx y hy u hu
    have heq : ∀ T ∈ C, coordSum T (x-chi u+chi v) = coordSum T x := by
      intro T hT
      have huT : u ∉ T := fun h => huU (hCU T hT h)
      have hvT : v ∉ T := by
        intro hvT
        have hh := hxmax T hT (x-chi u+chi v) hx'
        rw [coordSum_exchange,if_neg huT,if_pos hvT] at hh
        omega
      rw [coordSum_exchange,if_neg huT,if_neg hvT]
      simp
    have hmem : x-chi u+chi v ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨hx',?_⟩
      intro T hT a ha
      rw [heq T hT]
      exact hxmax T hT a ha
    have hm := hmin _ hmem
    rw [positiveDeviation_exchange x y u v hu hv] at hm
    omega
  refine ⟨x,hx,hxmax,?_⟩
  intro a ha
  rw [hxU]
  exact hymax a ha

/-- Every finite inclusion chain has a common rank-maximizing base. -/
theorem chain_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V))
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    ∃ x ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x := by
  classical
  revert hchain
  refine Finset.strongInductionOn C ?_
  intro C ih hchain
  by_cases hC : C.Nonempty
  · obtain ⟨U,hU,hUmax⟩ := Finset.exists_max_image C Finset.card hC
    have hall : ∀ T ∈ C, T ⊆ U := by
      intro T hT
      rcases hchain T hT U hU with h | h
      · exact h
      · have heq : U = T := Finset.eq_of_subset_of_card_le h (hUmax T hT)
        exact heq.symm.subset
    obtain ⟨z,hz,hzmax⟩ := ih (C.erase U) (Finset.erase_ssubset hU)
      (fun T hT W hW => hchain T (Finset.mem_of_mem_erase hT) W
        (Finset.mem_of_mem_erase hW))
    obtain ⟨x,hx,hxmax,hxU⟩ := extend_sum_maximizers hB (C.erase U) U
      (fun T hT => hall T (Finset.mem_of_mem_erase hT)) ⟨z,hz,hzmax⟩
    refine ⟨x,hx,?_⟩
    intro T hT a ha
    by_cases hTU : T = U
    · subst T
      exact hxU a ha
    · exact hxmax T (Finset.mem_erase.mpr ⟨hTU,hT⟩) a ha
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hC
    obtain ⟨x,hx⟩ := hB.1
    exact ⟨x,hx,by simp⟩


noncomputable def baseRank (B : Finset (V → ℤ)) (hne : B.Nonempty) (S : Finset V) : ℤ :=
  B.sup' hne (coordSum S)

theorem baseRank_submodular {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (X Y : Finset V) :
    baseRank B hB.1 (X ∪ Y) + baseRank B hB.1 (X ∩ Y) ≤
      baseRank B hB.1 X + baseRank B hB.1 Y := by
  obtain ⟨x,hx,hint,hunion⟩ := nested_sum_maximizers hB (X ∩ Y) (X ∪ Y)
    (fun i hi => Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hi).1))
  have hI : baseRank B hB.1 (X ∩ Y) = coordSum (X ∩ Y) x :=
    le_antisymm (Finset.sup'_le hB.1 _ hint) (Finset.le_sup' _ hx)
  have hU : baseRank B hB.1 (X ∪ Y) = coordSum (X ∪ Y) x :=
    le_antisymm (Finset.sup'_le hB.1 _ hunion) (Finset.le_sup' _ hx)
  have hX : coordSum X x ≤ baseRank B hB.1 X := Finset.le_sup' _ hx
  have hY : coordSum Y x ≤ baseRank B hB.1 Y := Finset.le_sup' _ hx
  have heq : coordSum (X ∪ Y) x + coordSum (X ∩ Y) x = coordSum X x + coordSum Y x := by
    exact Finset.sum_union_inter
  rw [hU,hI]
  omega


end SteinitzCoordinator

open scoped BigOperators

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Upper-level sum domination implies linear-objective domination.
The proof truncates the largest distinct weight and uses no order on V. -/
theorem upperLevel_dot_nonpos (W : Finset ℝ) :
    ∀ c d : V → ℝ, (∀ i, c i ∈ W) → (∑ i, d i) = 0 →
      (∀ t ∈ W, (∑ i ∈ Finset.univ.filter (fun i => t ≤ c i), d i) ≤ 0) →
      (∑ i, c i * d i) ≤ 0 := by
  classical
  refine Finset.strongInductionOn W ?_
  intro W ih c d hc hd hlevels
  have hW : W.Nonempty := ⟨c (Classical.arbitrary V), hc _⟩
  let M := W.max' hW
  have hMW : M ∈ W := Finset.max'_mem W hW
  have hcM : ∀ i, c i ≤ M := fun i => Finset.le_max' W (c i) (hc i)
  by_cases hW' : (W.erase M).Nonempty
  · let L := (W.erase M).max' hW'
    have hLW' : L ∈ W.erase M := Finset.max'_mem _ hW'
    have hLM : L ≤ M := Finset.le_max' W L (Finset.mem_of_mem_erase hLW')
    let c' : V → ℝ := fun i => min (c i) L
    have hc' : ∀ i, c' i ∈ W.erase M := by
      intro i
      by_cases he : c i = M
      · simpa only [c',he,min_eq_right hLM] using hLW'
      · have hi : c i ∈ W.erase M := Finset.mem_erase.mpr ⟨he,hc i⟩
        have hiL : c i ≤ L := Finset.le_max' _ _ hi
        simpa only [c',min_eq_left hiL] using hi
    have hlevels' : ∀ t ∈ W.erase M,
        (∑ i ∈ Finset.univ.filter (fun i => t ≤ c' i), d i) ≤ 0 := by
      intro t ht
      have htL : t ≤ L := Finset.le_max' _ _ ht
      have heq : Finset.univ.filter (fun i : V => t ≤ c' i) =
          Finset.univ.filter (fun i => t ≤ c i) := by
        ext i
        simp [c',htL]
      rw [heq]
      exact hlevels t (Finset.mem_of_mem_erase ht)
    have hind := ih (W.erase M) (Finset.erase_ssubset hMW) c' d hc' hd hlevels'
    have htop : (∑ i, if c i = M then d i else 0) ≤ 0 := by
      have heq : Finset.univ.filter (fun i : V => M ≤ c i) =
          Finset.univ.filter (fun i => c i = M) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => le_antisymm (hcM i) h, fun h => h ▸ le_rfl⟩
      have hh := hlevels M hMW
      rw [heq] at hh
      simpa only [Finset.sum_filter] using hh
    have hid : ∀ i, c i * d i = c' i * d i +
        (M-L) * (if c i = M then d i else 0) := by
      intro i
      by_cases he : c i = M
      · simp [c',he,min_eq_right hLM] ; ring
      · have hi : c i ∈ W.erase M := Finset.mem_erase.mpr ⟨he,hc i⟩
        have hiL : c i ≤ L := Finset.le_max' _ _ hi
        simp [c',min_eq_left hiL,he]
    have hsumid := congrArg (fun f : V → ℝ => ∑ i, f i) (funext hid)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumid
    rw [hsumid]
    exact add_nonpos hind (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hLM) htop)
  · have hempty : W.erase M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW'
    have hconst : ∀ i, c i = M := by
      intro i
      by_contra hi
      have hmem := Finset.mem_erase.mpr ⟨hi,hc i⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    simp_rw [hconst]
    simp only [← Finset.mul_sum,hd,mul_zero,le_refl]


end SteinitzCoordinator

/- COMPONENT: CoordinatorRankHull -/

open scoped BigOperators
open SteinitzExchange.Extension

namespace SteinitzCoordinator

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
lemma baseRank_univ_eq [Nonempty V] {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {y : V → ℤ} (hy : y ∈ B) : baseRank B hB.1 Finset.univ = ∑ i, y i := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    exact (base_sum_eq hB hx hy).le
  · exact Finset.le_sup' _ hy

def RealRankConstraints (B : Finset (V → ℤ)) (hne : B.Nonempty) (z : V → ℝ) : Prop :=
  (∀ S : Finset V, (∑ i ∈ S, z i) ≤ (baseRank B hne S : ℝ)) ∧
    (∑ i, z i) = (baseRank B hne Finset.univ : ℝ)

/-- Every objective on a rank-feasible point is dominated by a genuine base. -/
theorem objective_le_base_of_rank_constraints {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) (z : V → ℝ) (hz : RealRankConstraints B hB.1 z)
    (c : V → ℝ) : ∃ y ∈ B, (∑ i, c i * z i) ≤ ∑ i, c i * (y i : ℝ) := by
  classical
  let W : Finset ℝ := Finset.univ.image c
  let upper : ℝ → Finset V := fun t => Finset.univ.filter (fun i => t ≤ c i)
  let C : Finset (Finset V) := W.image upper
  have hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hU
    by_cases hst : s ≤ t
    · right
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hst.trans (Finset.mem_filter.mp hi).2⟩
    · left
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (lt_of_not_ge hst).le.trans (Finset.mem_filter.mp hi).2⟩
  obtain ⟨y,hy,hymax⟩ := chain_sum_maximizers hB C hchain
  let d : V → ℝ := fun i => z i - (y i : ℝ)
  have hzero : (∑ i, d i) = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, ← Int.cast_sum, hz.2, baseRank_univ_eq hB hy, sub_self]
  have hlevels : ∀ t ∈ W,
      (∑ i ∈ Finset.univ.filter (fun i => t ≤ c i), d i) ≤ 0 := by
    intro t ht
    have hT : upper t ∈ C := Finset.mem_image.mpr ⟨t,ht,rfl⟩
    have hrank : baseRank B hB.1 (upper t) = coordSum (upper t) y :=
      le_antisymm (Finset.sup'_le hB.1 _ (hymax (upper t) hT)) (Finset.le_sup' _ hy)
    have hh := hz.1 (upper t)
    rw [hrank] at hh
    change (∑ i ∈ upper t, d i) ≤ 0
    dsimp [d]
    rw [Finset.sum_sub_distrib]
    have hcast : (∑ i ∈ upper t, (y i : ℝ)) = (coordSum (upper t) y : ℝ) := by
      simp [coordSum]
    rw [hcast]
    exact sub_nonpos.mpr hh
  have hdot := upperLevel_dot_nonpos W c d
    (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hzero hlevels
  simp only [d,mul_sub,Finset.sum_sub_distrib] at hdot
  exact ⟨y,hy,sub_nonpos.mp hdot⟩

omit [Nonempty V] in
lemma linearMap_pi_dot [Nonempty V] (f : (V → ℝ) →ₗ[ℝ] ℝ) (z : V → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : V → ℝ) := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,mul_ite]
  calc
    f z = f (∑ i, z i • (Pi.single i 1 : V → ℝ)) := congrArg f hz
    _ = ∑ i, f (Pi.single i 1) * z i := by
      simp [map_sum,map_smul,smul_eq_mul,mul_comm]

/-- Rank inequalities cut out the real convex hull of a finite base set. -/
theorem mem_hull_of_rank_constraints {B : Finset (V → ℤ)}
    (hB : IsIntegralBaseSet B) (z : V → ℝ) (hz : RealRankConstraints B hB.1 z) :
    z ∈ hull B := by
  by_contra hnot
  have hfinite : (toReal '' (B : Set (V → ℤ))).Finite :=
    (Finset.finite_toSet B).image toReal
  have hclosed : IsClosed (hull B) := hfinite.isClosed_convexHull ℝ
  have hconv : Convex ℝ (hull B) := convex_convexHull ℝ _
  obtain ⟨f,r,hfr,hrz⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  let c : V → ℝ := fun i => f (Pi.single i 1)
  obtain ⟨y,hy,hle⟩ := objective_le_base_of_rank_constraints hB z hz c
  have hyHull : toReal y ∈ hull B := subset_convexHull ℝ _ ⟨y,hy,rfl⟩
  have hzDot := linearMap_pi_dot f.toLinearMap z
  have hyDot := linearMap_pi_dot f.toLinearMap (toReal y)
  have hleF : f z ≤ f (toReal y) := by
    change f.toLinearMap z ≤ f.toLinearMap (toReal y)
    rw [hzDot,hyDot]
    simpa only [c,toReal,ContinuousLinearMap.coe_coe] using hle
  exact (not_lt_of_ge hleF) ((hfr _ hyHull).trans hrz)


end SteinitzCoordinator

/- COMPONENT: SteinitzGreedyWitness -/

open scoped BigOperators

namespace SteinitzGreedy

variable {V : Type*} [DecidableEq V]

/-- Recursive greedy construction. Remove coordinates outside the requested tight
set first, so that the recursion makes that set an initial greedy segment. -/
theorem greedy_on_ground (f : Finset V → ℤ)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (hf0 : f ∅ = 0) :
    ∀ S X : Finset V, X ⊆ S → ∃ z : V → ℤ,
      (∀ v, v ∉ S → z v = 0) ∧
      (∀ T : Finset V, T ⊆ S → (∑ v ∈ T, z v) ≤ f T) ∧
      (∑ v ∈ S, z v) = f S ∧ (∑ v ∈ X, z v) = f X := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih X hXS
  by_cases hS : S = ∅
  · subst S
    have hX : X = ∅ := Finset.Subset.antisymm hXS (Finset.empty_subset _)
    subst X
    refine ⟨fun _ => 0, by simp, ?_, by simp [hf0], by simp [hf0]⟩
    intro T hT
    have hT' : T = ∅ := Finset.Subset.antisymm hT (Finset.empty_subset _)
    simp [hT', hf0]
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hex : ∃ u ∈ S, u ∉ X ∨ X = S := by
    by_cases he : X = S
    · obtain ⟨u, hu⟩ := hSne
      exact ⟨u, hu, Or.inr he⟩
    · have hn : ¬ S ⊆ X := by
        intro hSX
        exact he (Finset.Subset.antisymm hXS hSX)
      obtain ⟨u, huS, huX⟩ := Finset.not_subset.mp hn
      exact ⟨u, huS, Or.inl huX⟩
  obtain ⟨u, huS, huX⟩ := hex
  have hXerase : X.erase u ⊆ S.erase u := by
    intro v hv
    obtain ⟨hvu, hvX⟩ := Finset.mem_erase.mp hv
    exact Finset.mem_erase.mpr ⟨hvu, hXS hvX⟩
  obtain ⟨z, hzout, hz, hzS, hzX⟩ :=
    ih (S.erase u) (Finset.erase_ssubset huS) (X.erase u) hXerase
  let δ : ℤ := f S - f (S.erase u)
  let z' : V → ℤ := Function.update z u δ
  have hsum_mem (T : Finset V) (huT : u ∈ T) :
      (∑ v ∈ T, z' v) = δ + ∑ v ∈ T.erase u, z v := by
    simpa only [z', Finset.sdiff_singleton_eq_erase] using
      Finset.sum_update_of_mem huT z δ
  have hsum_not_mem (T : Finset V) (huT : u ∉ T) :
      (∑ v ∈ T, z' v) = ∑ v ∈ T, z v :=
    Finset.sum_update_of_notMem huT z δ
  have hz'S : (∑ v ∈ S, z' v) = f S := by
    rw [hsum_mem S huS, hzS]
    dsimp [δ]
    omega
  refine ⟨z', ?_, ?_, hz'S, ?_⟩
  · intro v hv
    have hvu : v ≠ u := by intro h; subst v; exact hv huS
    have hvS' : v ∉ S.erase u := fun h => hv (Finset.mem_of_mem_erase h)
    simp only [z', Function.update_of_ne hvu, hzout v hvS']
  · intro T hTS
    by_cases huT : u ∈ T
    · have herase : T.erase u ⊆ S.erase u := by
        intro v hv
        obtain ⟨hvu, hvT⟩ := Finset.mem_erase.mp hv
        exact Finset.mem_erase.mpr ⟨hvu, hTS hvT⟩
      have hunion : S.erase u ∪ T = S := by
        ext v
        simp only [Finset.mem_union, Finset.mem_erase]
        constructor
        · rintro (⟨_, hv⟩ | hv)
          · exact hv
          · exact hTS hv
        · intro hv
          by_cases he : v = u
          · exact Or.inr (he.symm ▸ huT)
          · exact Or.inl ⟨he, hv⟩
      have hinter : S.erase u ∩ T = T.erase u := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hvu, _⟩, hvT⟩
          exact ⟨hvu, hvT⟩
        · rintro ⟨hvu, hvT⟩
          exact ⟨⟨hvu, hTS hvT⟩, hvT⟩
      have hsub := hf (S.erase u) T
      rw [hunion, hinter] at hsub
      have hrec := hz (T.erase u) herase
      rw [hsum_mem T huT]
      dsimp [δ]
      omega
    · have hTsub : T ⊆ S.erase u := by
        intro v hvT
        refine Finset.mem_erase.mpr ⟨?_, hTS hvT⟩
        intro he
        exact huT (he ▸ hvT)
      rw [hsum_not_mem T huT]
      exact hz T hTsub
  · rcases huX with huX | rfl
    · rw [hsum_not_mem X huX]
      simpa only [Finset.erase_eq_of_notMem huX] using hzX
    · exact hz'S

theorem exists_integer_base_tight [Fintype V] (f : Finset V → ℤ)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (hf0 : f ∅ = 0)
    (X : Finset V) : ∃ z : V → ℤ,
      (∀ T : Finset V, (∑ v ∈ T, z v) ≤ f T) ∧
      (∑ v, z v) = f Finset.univ ∧ (∑ v ∈ X, z v) = f X := by
  obtain ⟨z, _, hz, hzS, hzX⟩ :=
    greedy_on_ground f hf hf0 Finset.univ X (Finset.subset_univ X)
  exact ⟨z, fun T => hz T (Finset.subset_univ T), hzS, hzX⟩

theorem submodular_representation_unique [Fintype V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) (f : Finset V → ℤ)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (hf0 : f ∅ = 0)
    (hB : ∀ z : V → ℤ, z ∈ B ↔
      (∀ T : Finset V, (∑ v ∈ T, z v) ≤ f T) ∧ (∑ v, z v) = f Finset.univ) :
    ∀ X : Finset V, f X = B.sup' hne (fun z => ∑ v ∈ X, z v) := by
  intro X
  obtain ⟨z, hz, hzS, hzX⟩ := exists_integer_base_tight f hf hf0 X
  have hzB : z ∈ B := (hB z).mpr ⟨hz, hzS⟩
  apply le_antisymm
  · rw [← hzX]
    exact Finset.le_sup' (fun z => ∑ v ∈ X, z v) hzB
  · apply Finset.sup'_le
    intro z hzB
    exact ((hB z).mp hzB).1 X


theorem exists_integer_superbase_tight [Fintype V] (g : Finset V → ℤ)
    (hg : ∀ X Y, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)) (hg0 : g ∅ = 0)
    (X : Finset V) : ∃ z : V → ℤ,
      (∀ T : Finset V, g T ≤ ∑ v ∈ T, z v) ∧
      (∑ v, z v) = g Finset.univ ∧ (∑ v ∈ X, z v) = g X := by
  have hf : ∀ X Y, (-g (X ∪ Y)) + (-g (X ∩ Y)) ≤ (-g X) + (-g Y) := by
    intro X Y
    have := hg X Y
    omega
  obtain ⟨z, hz, hzS, hzX⟩ := exists_integer_base_tight (fun T => -g T) hf
    (by simp [hg0]) X
  refine ⟨fun v => -z v, ?_, ?_, ?_⟩
  · intro T
    rw [Finset.sum_neg_distrib]
    have := hz T
    omega
  · rw [Finset.sum_neg_distrib, hzS]
    simp
  · rw [Finset.sum_neg_distrib, hzX]
    simp

theorem supermodular_representation_unique [Fintype V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) (g : Finset V → ℤ)
    (hg : ∀ X Y, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)) (hg0 : g ∅ = 0)
    (hB : ∀ z : V → ℤ, z ∈ B ↔
      (∀ T : Finset V, g T ≤ ∑ v ∈ T, z v) ∧ (∑ v, z v) = g Finset.univ) :
    ∀ X : Finset V, g X = B.inf' hne (fun z => ∑ v ∈ X, z v) := by
  intro X
  obtain ⟨z, hz, hzS, hzX⟩ := exists_integer_superbase_tight g hg hg0 X
  have hzB : z ∈ B := (hB z).mpr ⟨hz, hzS⟩
  apply le_antisymm
  · apply Finset.le_inf'
    intro z hzB
    exact ((hB z).mp hzB).1 X
  · rw [← hzX]
    exact Finset.inf'_le (fun z => ∑ v ∈ X, z v) hzB


end SteinitzGreedy

/- COMPONENT: SteinitzSubmodularConverse -/

set_option autoImplicit false

open Finset SteinitzExchange.Extension

namespace SteinitzConverse

variable {V : Type*} [Fintype V] [DecidableEq V]

def setSum (x : V → ℤ) (S : Finset V) : ℤ := ∑ i ∈ S, x i

omit [Fintype V] in
lemma setSum_exchange [Fintype V] (x : V → ℤ) (u v : V) (S : Finset V) :
    setSum (x - chi u + chi v) S =
      setSum x S - (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  simp [setSum, Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

omit [Fintype V] in
lemma setSum_union_inter [Fintype V] (x : V → ℤ) (S T : Finset V) :
    setSum x (S ∪ T) + setSum x (S ∩ T) = setSum x S + setSum x T :=
  Finset.sum_union_inter

lemma tight_union (f : Finset V → ℤ)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T)
    (x : V → ℤ) (hx : ∀ S, setSum x S ≤ f S)
    {S T : Finset V} (hS : setSum x S = f S) (hT : setSum x T = f T) :
    setSum x (S ∪ T) = f (S ∪ T) := by
  have hident := setSum_union_inter x S T
  have hs := hsub S T
  have hU := hx (S ∪ T)
  have hI := hx (S ∩ T)
  omega

lemma tight_biUnion (f : Finset V → ℤ)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T)
    (hf0 : f ∅ = 0) (x : V → ℤ) (hx : ∀ S, setSum x S ≤ f S)
    (C : Finset (Finset V)) (hC : ∀ S ∈ C, setSum x S = f S) :
    setSum x (C.biUnion id) = f (C.biUnion id) := by
  induction C using Finset.induction_on with
  | empty => simp [setSum, hf0]
  | @insert S C hSC ih =>
    rw [Finset.biUnion_insert]
    exact tight_union f hsub x hx (hC S (mem_insert_self _ _))
      (ih (fun T hT => hC T (mem_insert_of_mem hT)))

/-- A normalized submodular integer base system satisfies the one-unit exchange
    property. Only tight-set closure and integrality of the one-unit slack are used. -/
theorem submodular_base_exchange (f : Finset V → ℤ)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) (hf0 : f ∅ = 0)
    (x y : V → ℤ) (hx : ∀ S, setSum x S ≤ f S) (hy : ∀ S, setSum y S ≤ f S)
    (htotal : setSum x univ = setSum y univ) (u : V) (hu : y u < x u) :
    ∃ v : V, x v < y v ∧ ∀ S, setSum (x - chi u + chi v) S ≤ f S := by
  classical
  by_contra hno
  have hbad : ∀ v, x v < y v →
      ∃ S : Finset V, u ∉ S ∧ v ∈ S ∧ setSum x S = f S := by
    intro v hv
    have hnot : ¬ ∀ S, setSum (x - chi u + chi v) S ≤ f S := by
      intro hvok
      exact hno ⟨v, hv, hvok⟩
    obtain ⟨S, hnotS⟩ := not_forall.mp hnot
    have hS := lt_of_not_ge hnotS
    have hxS := hx S
    rw [setSum_exchange] at hS
    by_cases huS : u ∈ S
    · by_cases hvS : v ∈ S <;> simp only [huS, hvS, if_true, if_false] at hS <;> omega
    · by_cases hvS : v ∈ S
      · refine ⟨S, huS, hvS, ?_⟩
        simp only [huS, hvS, if_true, if_false] at hS
        omega
      · simp only [huS, hvS, if_false] at hS
        omega
  let C : Finset (Finset V) := univ.powerset.filter fun S => u ∉ S ∧ setSum x S = f S
  let U : Finset V := C.biUnion id
  have hUtight : setSum x U = f U :=
    tight_biUnion f hsub hf0 x hx C (fun S hS => (mem_filter.mp hS).2.2)
  have huU : u ∉ U := by
    intro h
    obtain ⟨S, hS, huS⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hS).2.1 huS
  have hDU : ∀ v, x v < y v → v ∈ U := by
    intro v hv
    obtain ⟨S, huS, hvS, hStight⟩ := hbad v hv
    apply mem_biUnion.mpr
    refine ⟨S, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ S), huS, hStight⟩, hvS⟩
  have hcomp : setSum y Uᶜ < setSum x Uᶜ := by
    apply Finset.sum_lt_sum
    · intro v hv
      have hn : ¬ x v < y v := fun hlt => (mem_compl.mp hv) (hDU v hlt)
      exact le_of_not_gt hn
    · exact ⟨u, mem_compl.mpr huU, hu⟩
  have hcx := Finset.sum_add_sum_compl U x
  have hcy := Finset.sum_add_sum_compl U y
  have hyU := hy U
  change setSum x U + setSum x Uᶜ = setSum x univ at hcx
  change setSum y U + setSum y Uᶜ = setSum y univ at hcy
  omega

theorem isIntegralBaseSet_of_submodular_representation
    (B : Finset (V → ℤ)) (hne : B.Nonempty) (f : Finset V → ℤ)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) (hf0 : f ∅ = 0)
    (hrep : ∀ x : V → ℤ, x ∈ B ↔
      (∀ S : Finset V, setSum x S ≤ f S) ∧ setSum x univ = f univ) :
    IsIntegralBaseSet B := by
  refine ⟨hne, ?_⟩
  intro x hx y hy u hu
  obtain ⟨hxineq, hxtotal⟩ := (hrep x).mp hx
  obtain ⟨hyineq, hytotal⟩ := (hrep y).mp hy
  have hu' : y u < x u := by
    change 0 < x u - y u at hu
    omega
  obtain ⟨v, hv, hz⟩ := submodular_base_exchange f hsub hf0 x y hxineq hyineq
    (hxtotal.trans hytotal.symm) u hu'
  refine ⟨v, ?_, (hrep _).mpr ⟨hz, ?_⟩⟩
  · change x v - y v < 0
    omega
  · rw [setSum_exchange]
    simpa using hxtotal


end SteinitzConverse

/- COMPONENT: SteinitzComplementTransform -/

set_option autoImplicit false

open Finset SteinitzConverse

namespace SteinitzComplement

variable {V : Type*} [Fintype V] [DecidableEq V]

def transform (f : Finset V → ℤ) (S : Finset V) : ℤ := f univ - f Sᶜ

def UpperSystem (f : Finset V → ℤ) (x : V → ℤ) : Prop :=
  (∀ S, setSum x S ≤ f S) ∧ setSum x univ = f univ

def LowerSystem (g : Finset V → ℤ) (x : V → ℤ) : Prop :=
  (∀ S, g S ≤ setSum x S) ∧ setSum x univ = g univ

@[simp] lemma transform_empty (f : Finset V → ℤ) : transform f ∅ = 0 := by
  simp [transform]

lemma transform_univ (f : Finset V → ℤ) (h0 : f ∅ = 0) : transform f univ = f univ := by
  simp [transform, h0]

lemma transform_involutive (f : Finset V → ℤ) (h0 : f ∅ = 0) :
    transform (transform f) = f := by
  funext S
  simp [transform, h0]

lemma supermodular_transform (f : Finset V → ℤ)
    (hf : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) :
    ∀ S T, transform f S + transform f T ≤ transform f (S ∪ T) + transform f (S ∩ T) := by
  intro S T
  have h := hf Sᶜ Tᶜ
  simp only [transform, Finset.compl_union, Finset.compl_inter]
  omega

lemma submodular_transform (g : Finset V → ℤ)
    (hg : ∀ S T, g S + g T ≤ g (S ∪ T) + g (S ∩ T)) :
    ∀ S T, transform g (S ∪ T) + transform g (S ∩ T) ≤ transform g S + transform g T := by
  intro S T
  have h := hg Sᶜ Tᶜ
  simp only [transform, Finset.compl_union, Finset.compl_inter]
  omega

lemma setSum_add_compl (x : V → ℤ) (S : Finset V) :
    setSum x S + setSum x Sᶜ = setSum x univ := Finset.sum_add_sum_compl S x

theorem upper_iff_lower_transform (f : Finset V → ℤ) (h0 : f ∅ = 0) (x : V → ℤ) :
    UpperSystem f x ↔ LowerSystem (transform f) x := by
  constructor
  · rintro ⟨hx, ht⟩
    refine ⟨fun S => ?_, ?_⟩
    · have hSc := hx Sᶜ
      have hc := setSum_add_compl x S
      unfold transform
      omega
    · simpa only [transform_univ f h0] using ht
  · rintro ⟨hx, ht⟩
    have ht' : setSum x univ = f univ := by
      simpa only [transform_univ f h0] using ht
    refine ⟨fun S => ?_, ht'⟩
    have hSc := hx Sᶜ
    simp only [transform, compl_compl] at hSc
    have hc := setSum_add_compl x S
    omega

theorem lower_iff_upper_transform (g : Finset V → ℤ) (h0 : g ∅ = 0) (x : V → ℤ) :
    LowerSystem g x ↔ UpperSystem (transform g) x := by
  simpa only [transform_involutive g h0] using
    (upper_iff_lower_transform (transform g) (transform_empty g) x).symm

/-- Canonical upper bounds on complementary sets give canonical lower bounds.
    This transfers the uniqueness clause from submodular to supermodular systems. -/
theorem canonical_lower_of_canonical_upper (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (f : Finset V → ℤ) (hf0 : f ∅ = 0)
    (hfeasible : ∀ x ∈ B, UpperSystem f x)
    (hcanonical : ∀ S, f S = B.sup' hne (fun x => setSum x S)) (S : Finset V) :
    transform f S = B.inf' hne (fun x => setSum x S) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro x hx
    exact ((upper_iff_lower_transform f hf0 x).mp (hfeasible x hx)).1 S
  · obtain ⟨x, hx, hmax⟩ := B.exists_mem_eq_sup' hne (fun x => setSum x Sᶜ)
    have ht := (hfeasible x hx).2
    have hc := setSum_add_compl x S
    have hfSc : f Sᶜ = setSum x Sᶜ := (hcanonical Sᶜ).trans hmax
    have hxS : setSum x S = transform f S := by
      unfold transform
      omega
    calc
      B.inf' hne (fun x => setSum x S) ≤ setSum x S := Finset.inf'_le _ hx
      _ = transform f S := hxS

theorem canonical_lower_of_transformed_upper (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (g : Finset V → ℤ) (hg0 : g ∅ = 0)
    (hfeasible : ∀ x ∈ B, LowerSystem g x)
    (hcanonical : ∀ S, transform g S = B.sup' hne (fun x => setSum x S)) (S : Finset V) :
    g S = B.inf' hne (fun x => setSum x S) := by
  have h := canonical_lower_of_canonical_upper B hne (transform g) (transform_empty g)
    (fun x hx => (lower_iff_upper_transform g hg0 x).mp (hfeasible x hx)) hcanonical S
  simpa only [transform_involutive g hg0] using h


end SteinitzComplement

/- COMPONENT: SteinitzFinalAssembly -/

set_option autoImplicit false

namespace SteinitzFinal

open SteinitzComplement

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
lemma integralBaseSet_bridge [Fintype V] [Nonempty V] (B : Finset (V → ℤ)) :
    SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      SteinitzExchange.Extension.IsIntegralBaseSet B := Iff.rfl

theorem integral_base_iff_upper (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, SteinitzExchange.Duality.IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔ UpperSystem f x := by
  constructor
  · intro hB
    have hE := (integralBaseSet_bridge B).mp hB
    let f : Finset V → ℤ := SteinitzCoordinator.baseRank B hE.1
    refine ⟨f, SteinitzCoordinator.baseRank_submodular hE, ?_, ?_⟩
    · change B.sup' hE.1 (SteinitzCoordinator.coordSum ∅) = 0
      apply Finset.sup'_eq_of_forall
      intro x hx
      simp [SteinitzCoordinator.coordSum]
    · intro x
      constructor
      · intro hx
        refine ⟨fun S => ?_, ?_⟩
        · exact Finset.le_sup' (SteinitzCoordinator.coordSum S) hx
        · exact (SteinitzCoordinator.baseRank_univ_eq hE hx).symm
      · rintro ⟨hx, ht⟩
        have hr : SteinitzCoordinator.RealRankConstraints B hE.1
            (SteinitzExchange.Extension.toReal x) := by
          refine ⟨fun S => ?_, ?_⟩
          · have hi : (∑ i ∈ S, x i) ≤ SteinitzCoordinator.baseRank B hE.1 S := hx S
            change (∑ i ∈ S, (x i : ℝ)) ≤ (SteinitzCoordinator.baseRank B hE.1 S : ℝ)
            exact_mod_cast hi
          · have hi : (∑ i, x i) = SteinitzCoordinator.baseRank B hE.1 Finset.univ := ht
            change (∑ i, (x i : ℝ)) = (SteinitzCoordinator.baseRank B hE.1 Finset.univ : ℝ)
            exact_mod_cast hi
        exact (SteinitzExchange.Extension.toReal_mem_hull_iff_checked B hE x).mp
          (SteinitzCoordinator.mem_hull_of_rank_constraints hE _ hr)
  · rintro ⟨f, hf, hf0, hrep⟩
    apply (integralBaseSet_bridge B).mpr
    exact SteinitzConverse.isIntegralBaseSet_of_submodular_representation B hne f hf hf0 hrep

theorem integral_base_iff_lower (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, SteinitzExchange.Duality.IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔ LowerSystem g x := by
  constructor
  · intro hB
    obtain ⟨f, hf, hf0, hrep⟩ := (integral_base_iff_upper B hne).mp hB
    refine ⟨transform f, supermodular_transform f hf, transform_empty f, fun x => ?_⟩
    exact (hrep x).trans (upper_iff_lower_transform f hf0 x)
  · rintro ⟨g, hg, hg0, hrep⟩
    apply (integral_base_iff_upper B hne).mpr
    refine ⟨transform g, submodular_transform g hg, transform_empty g, fun x => ?_⟩
    exact (hrep x).trans (lower_iff_upper_transform g hg0 x)

omit [Nonempty V] in
theorem unique_upper [Nonempty V] (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (f : Finset V → ℤ) (hf : SteinitzExchange.Duality.IsSubmodular f) (hf0 : f ∅ = 0)
    (hrep : ∀ x : V → ℤ, x ∈ B ↔ UpperSystem f x) :
    ∀ S : Finset V, f S = B.sup' hne (fun x => SteinitzExchange.Duality.sumOn x S) := by
  exact SteinitzGreedy.submodular_representation_unique B hne f hf hf0 hrep

theorem unique_lower (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (g : Finset V → ℤ) (hg : SteinitzExchange.Duality.IsSupermodular g) (hg0 : g ∅ = 0)
    (hrep : ∀ x : V → ℤ, x ∈ B ↔ LowerSystem g x) :
    ∀ S : Finset V, g S = B.inf' hne (fun x => SteinitzExchange.Duality.sumOn x S) := by
  have hupper : ∀ x : V → ℤ, x ∈ B ↔ UpperSystem (transform g) x :=
    fun x => (hrep x).trans (lower_iff_upper_transform g hg0 x)
  have hcanonical := unique_upper B hne (transform g)
    (submodular_transform g hg) (transform_empty g) hupper
  intro S
  exact canonical_lower_of_transformed_upper B hne g hg0
    (fun x hx => (hrep x).mp hx) hcanonical S

end SteinitzFinal


theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, SteinitzExchange.Duality.IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, SteinitzExchange.Duality.sumOn x X ≤ f X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = f Finset.univ) ∧
    (SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, SteinitzExchange.Duality.IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ SteinitzExchange.Duality.sumOn x X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, SteinitzExchange.Duality.IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, SteinitzExchange.Duality.sumOn x X ≤ f X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => SteinitzExchange.Duality.sumOn x X)) ∧
    (∀ g : Finset V → ℤ, SteinitzExchange.Duality.IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ SteinitzExchange.Duality.sumOn x X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => SteinitzExchange.Duality.sumOn x X)) := by
  exact ⟨SteinitzFinal.integral_base_iff_upper B hne,
    SteinitzFinal.integral_base_iff_lower B hne,
    SteinitzFinal.unique_upper B hne,
    SteinitzFinal.unique_lower B hne⟩


end AttributedSteinitz.Duality

section
open SteinitzExchange.LocalSupermod
theorem SteinitzExchange.Duality.baseSet_iff_submodular_system {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, SteinitzExchange.Duality.IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, SteinitzExchange.Duality.sumOn x X ≤ f X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = f Finset.univ) ∧
    (SteinitzExchange.Duality.IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, SteinitzExchange.Duality.IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ SteinitzExchange.Duality.sumOn x X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, SteinitzExchange.Duality.IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, SteinitzExchange.Duality.sumOn x X ≤ f X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => SteinitzExchange.Duality.sumOn x X)) ∧
    (∀ g : Finset V → ℤ, SteinitzExchange.Duality.IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ SteinitzExchange.Duality.sumOn x X) ∧ SteinitzExchange.Duality.sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => SteinitzExchange.Duality.sumOn x X)) := by
  exact AttributedSteinitz.Duality.solution B hne
end


namespace AttributedSteinitz.Support
-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.baseSet_iff_support_matroidal
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T23:18:32.245978+00:00
-- url     : https://prove2.me/submissions/d3cc98d3-b194-4b41-86e5-92d41ac5edb9


set_option autoImplicit false

/- Component: Solutions/SteinitzLocalSupport.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

open SteinitzExchange.LocalSupermod

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma supportMin_le_pairing [DecidableEq V] (B : Finset (V → ℤ)) (p : V → ℝ)
    {x : V → ℤ} (hx : x ∈ B) : supportMin B p ≤ pairing p (toReal x) :=
  ciInf_le (Set.finite_range (fun a : (B : Set (V → ℤ)) => pairing p (toReal a.val))).bddBelow ⟨x,hx⟩

omit [DecidableEq V] in
lemma le_supportMin [DecidableEq V] (B : Finset (V → ℤ)) (hne : B.Nonempty) (p : V → ℝ) (a : ℝ)
    (ha : ∀ x ∈ B, a ≤ pairing p (toReal x)) : a ≤ supportMin B p := by
  let : Nonempty (B : Set (V → ℤ)) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  exact le_ciInf (fun x => ha x.val x.property)

lemma supportMin_eq_of_minimum (B : Finset (V → ℤ)) (p : V → ℝ)
    {x : V → ℤ} (hx : x ∈ B) (hmin : ∀ y ∈ B, pairing p (toReal x) ≤ pairing p (toReal y)) :
    supportMin B p = pairing p (toReal x) :=
  le_antisymm (supportMin_le_pairing B p hx) (le_supportMin B ⟨x,hx⟩ p _ hmin)

lemma supportMin_attained (B : Finset (V → ℤ)) (hne : B.Nonempty) (p : V → ℝ) :
    ∃ x ∈ B, supportMin B p = pairing p (toReal x) := by
  classical
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image B (fun x => pairing p (toReal x)) hne
  exact ⟨x,hx,supportMin_eq_of_minimum B p hx hmin⟩

omit [DecidableEq V] in
lemma pairing_smul_left [DecidableEq V] (c : ℝ) (p b : V → ℝ) :
    pairing (c • p) b = c * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma pairing_charVec (X : Finset V) (x : V → ℤ) :
    pairing (charVec X) (toReal x) = (sumOn x X : ℝ) := by
  simp [pairing,charVec,toReal,sumOn,Finset.sum_ite_mem]

lemma supportMin_posHomogeneous (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    IsPosHomogeneous (supportMin B) := by
  intro c hc p
  obtain ⟨x,hx,heq⟩ := supportMin_attained B hne p
  rw [heq]
  rw [← pairing_smul_left]
  apply supportMin_eq_of_minimum B (c • p) hx
  intro y hy
  simp only [pairing_smul_left]
  exact mul_le_mul_of_nonneg_left (heq ▸ supportMin_le_pairing B p hy) hc.le

lemma supportMin_charVec (B : Finset (V → ℤ)) (hne : B.Nonempty) (X : Finset V) :
    supportMin B (charVec X) = ((B.inf' hne (fun x => sumOn x X) : ℤ) : ℝ) := by
  classical
  obtain ⟨x,hx,heq⟩ := B.exists_mem_eq_inf' hne (fun x => sumOn x X)
  rw [heq]
  rw [← pairing_charVec]
  apply supportMin_eq_of_minimum B (charVec X) hx
  intro y hy
  simp only [pairing_charVec]
  have h := B.inf'_le (fun x => sumOn x X) hy
  rw [heq] at h
  exact_mod_cast h


end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzChainTelescoping.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

def chainCoefficient {n : ℕ} (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  p j - if hj : (j : ℕ) + 1 < n then p ⟨(j : ℕ) + 1, hj⟩ else 0

lemma next_lastCases {n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    Fin.lastCases (0 : ℝ) p j.succ =
      if hj : (j : ℕ) + 1 < n then p ⟨(j : ℕ) + 1, hj⟩ else 0 := by
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h]
    have he : j.succ = (⟨(j : ℕ) + 1, h⟩ : Fin n).castSucc := by
      apply Fin.ext
      rfl
    rw [he, Fin.lastCases_castSucc]
  · rw [dif_neg h]
    have he : j.succ = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [he, Fin.lastCases_last]

lemma chainCoefficient_suffix {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j => i ≤ j), chainCoefficient p j) = p i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hs : Finset.univ.filter (fun j : Fin (n+1) => i ≤ j) =
        Finset.Icc i (Fin.last n) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Icc]
      exact ⟨fun h => ⟨h,Fin.le_last j⟩, fun h => h.1⟩
    rw [hs]
    let q : Fin (n+2) → ℝ := fun j => Fin.lastCases (0 : ℝ) p j
    have ht := Fin.sum_Icc_sub (M := ℝ) (Fin.le_last i)
      (fun j : Fin (n+2) => -(q j))
    calc
      (∑ j ∈ Finset.Icc i (Fin.last n), chainCoefficient p j) =
          ∑ j ∈ Finset.Icc i (Fin.last n),
            ((-(q j.succ)) - (-(q j.castSucc))) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [q]
        rw [Fin.lastCases_castSucc, next_lastCases]
        simp only [chainCoefficient]
        ring
      _ = p i := by simpa [q] using ht

lemma weighted_chain_expansion {n : ℕ} (p x : Fin n → ℝ) :
    (∑ i, p i * x i) =
      ∑ j, chainCoefficient p j * ∑ i ∈ Finset.univ.filter (fun i => i ≤ j), x i := by
  classical
  symm
  simp only [Finset.sum_filter, Finset.mul_sum]
  calc
    (∑ j, ∑ i, chainCoefficient p j * (if i ≤ j then x i else 0)) =
        ∑ i, ∑ j, if i ≤ j then chainCoefficient p j * x i else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = ∑ i, p i * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, ← Finset.sum_mul, chainCoefficient_suffix]


end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalChainCore.lean -/
section

set_option autoImplicit false
open scoped BigOperators
open SteinitzExchange.Extension

namespace SteinitzLocalRepairChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def positiveDeviation (x y : V → ℤ) : ℤ :=
  ∑ w, max (x w - y w) 0

omit [Nonempty V] in
theorem positiveDeviation_exchange [Nonempty V] (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    positiveDeviation (x - chi u + chi v) y = positiveDeviation x y - 1 := by
  have huv : u ≠ v := by
    intro h
    subst v
    omega
  have hpoint : ∀ w, max ((x - chi u + chi v) w - y w) 0 =
      max (x w - y w) 0 - (if w = u then 1 else 0) := by
    intro w
    by_cases hwu : w = u
    · subst w
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
        if_neg huv]
      change 0 < x u - y u at hu
      omega
    · by_cases hwv : w = v
      · subst w
        simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
          if_neg hwu, sub_zero]
        change x v - y v < 0 at hv
        omega
      · simp [Pi.add_apply, Pi.sub_apply, chi, hwu, hwv]
  simp only [positiveDeviation, hpoint, Finset.sum_sub_distrib]
  simp

/-- Constant totals from the public base-polytope characterization. -/
theorem base_sum_eq {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) :
    (∑ v, x v) = ∑ v, y v := by
  obtain ⟨f,hf,hf0,hrep⟩ :=
    (SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).1.mp hB
  have hxsum := ((hrep x).mp hx).2
  have hysum := ((hrep y).mp hy).2
  exact hxsum.trans hysum.symm

def coordSum (S : Finset V) (x : V → ℤ) : ℤ := ∑ i ∈ S, x i

omit [Fintype V] [Nonempty V] in
lemma coordSum_exchange [Fintype V] [Nonempty V] (S : Finset V) (x : V → ℤ) (u v : V) :
    coordSum S (x - chi u + chi v) =
      coordSum S x - (if u ∈ S then 1 else 0) + (if v ∈ S then 1 else 0) := by
  simp [coordSum, Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma exists_surplus_outside {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B) (U : Finset V)
    (hlt : coordSum U x < coordSum U y) :
    ∃ i, i ∉ U ∧ 0 < (x-y) i := by
  by_contra hn
  have hcomp : (∑ i ∈ Uᶜ, x i) ≤ ∑ i ∈ Uᶜ, y i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiU : i ∉ U := Finset.mem_compl.mp hi
    by_contra hnot
    apply hn
    refine ⟨i,hiU,?_⟩
    change 0 < x i - y i
    omega
  have ht := base_sum_eq hB hx hy
  have hcx := Finset.sum_add_sum_compl U (fun i => x i)
  have hcy := Finset.sum_add_sum_compl U (fun i => y i)
  unfold coordSum at hlt
  omega

/-- Extend a previously feasible family of tight maxima by a containing set. -/
theorem extend_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V)) (U : Finset V) (hCU : ∀ T ∈ C, T ⊆ U)
    (hprior : ∃ z ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T z) :
    ∃ x ∈ B, (∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x) ∧
      (∀ a ∈ B, coordSum U a ≤ coordSum U x) := by
  classical
  obtain ⟨z,hz,hzmax⟩ := hprior
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image B (coordSum U) hB.1
  let S := B.filter (fun x => ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x)
  have hS : S.Nonempty := ⟨z,Finset.mem_filter.mpr ⟨hz,hzmax⟩⟩
  obtain ⟨x,hxS,hmin⟩ := Finset.exists_min_image S
    (fun x => positiveDeviation x y) hS
  have hx : x ∈ B := (Finset.mem_filter.mp hxS).1
  have hxmax := (Finset.mem_filter.mp hxS).2
  have hxU : coordSum U x = coordSum U y := by
    by_contra hne
    have hlt : coordSum U x < coordSum U y := by
      have := hymax x hx
      omega
    obtain ⟨u,huU,hu⟩ := exists_surplus_outside hB hx hy U hlt
    obtain ⟨v,hv,hx'⟩ := hB.2 x hx y hy u hu
    have heq : ∀ T ∈ C, coordSum T (x-chi u+chi v) = coordSum T x := by
      intro T hT
      have huT : u ∉ T := fun h => huU (hCU T hT h)
      have hvT : v ∉ T := by
        intro hvT
        have hh := hxmax T hT (x-chi u+chi v) hx'
        rw [coordSum_exchange,if_neg huT,if_pos hvT] at hh
        omega
      rw [coordSum_exchange,if_neg huT,if_neg hvT]
      simp
    have hmem : x-chi u+chi v ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨hx',?_⟩
      intro T hT a ha
      rw [heq T hT]
      exact hxmax T hT a ha
    have hm := hmin _ hmem
    rw [positiveDeviation_exchange x y u v hu hv] at hm
    omega
  refine ⟨x,hx,hxmax,?_⟩
  intro a ha
  rw [hxU]
  exact hymax a ha

/-- Every finite inclusion chain has a common rank-maximizing base. -/
theorem chain_sum_maximizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V))
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    ∃ x ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T a ≤ coordSum T x := by
  classical
  revert hchain
  refine Finset.strongInductionOn C ?_
  intro C ih hchain
  by_cases hC : C.Nonempty
  · obtain ⟨U,hU,hUmax⟩ := Finset.exists_max_image C Finset.card hC
    have hall : ∀ T ∈ C, T ⊆ U := by
      intro T hT
      rcases hchain T hT U hU with h | h
      · exact h
      · have heq : U = T := Finset.eq_of_subset_of_card_le h (hUmax T hT)
        exact heq.symm.subset
    obtain ⟨z,hz,hzmax⟩ := ih (C.erase U) (Finset.erase_ssubset hU)
      (fun T hT W hW => hchain T (Finset.mem_of_mem_erase hT) W
        (Finset.mem_of_mem_erase hW))
    obtain ⟨x,hx,hxmax,hxU⟩ := extend_sum_maximizers hB (C.erase U) U
      (fun T hT => hall T (Finset.mem_of_mem_erase hT)) ⟨z,hz,hzmax⟩
    refine ⟨x,hx,?_⟩
    intro T hT a ha
    by_cases hTU : T = U
    · subst T
      exact hxU a ha
    · exact hxmax T (Finset.mem_erase.mpr ⟨hTU,hT⟩) a ha
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hC
    obtain ⟨x,hx⟩ := hB.1
    exact ⟨x,hx,by simp⟩


end SteinitzLocalRepairChain
end

/- Component: Solutions/SteinitzChainMinimizers.lean -/
section

set_option autoImplicit false

namespace SteinitzLocalRepair

open SteinitzExchange.Extension SteinitzLocalRepairChain

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Complementing a finite inclusion chain converts simultaneous maxima to minima,
since every two members of an integral base set have the same total sum. -/
theorem chain_sum_minimizers {B : Finset (V → ℤ)} (hB : IsIntegralBaseSet B)
    (C : Finset (Finset V))
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    ∃ x ∈ B, ∀ T ∈ C, ∀ a ∈ B, coordSum T x ≤ coordSum T a := by
  classical
  let D : Finset (Finset V) := C.image (fun T => Tᶜ)
  have hD : ∀ T ∈ D, ∀ U ∈ D, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hU
    rcases hchain S hS R hR with h | h
    · right
      intro v hv
      exact Finset.mem_compl.mpr (fun hvS => Finset.mem_compl.mp hv (h hvS))
    · left
      intro v hv
      exact Finset.mem_compl.mpr (fun hvR => Finset.mem_compl.mp hv (h hvR))
  obtain ⟨x,hx,hmax⟩ := chain_sum_maximizers hB D hD
  refine ⟨x,hx,?_⟩
  intro T hT a ha
  have hcomp := hmax Tᶜ (Finset.mem_image.mpr ⟨T,hT,rfl⟩) a ha
  have htotal := SteinitzLocalRepairChain.base_sum_eq hB hx ha
  have hcx := Finset.sum_add_sum_compl T (fun v => x v)
  have hca := Finset.sum_add_sum_compl T (fun v => a v)
  unfold coordSum at hcomp ⊢
  omega


end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalForward.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair

open SteinitzExchange.LocalSupermod

variable {V : Type*} [Fintype V] [DecidableEq V]

def chainPrefix (σ : Fin (Fintype.card V) ≃ V) (j : Fin (Fintype.card V)) : Finset V :=
  Finset.univ.filter (fun v => σ.symm v ≤ j)

omit [DecidableEq V] in
lemma chainPrefix_mono [DecidableEq V] (σ : Fin (Fintype.card V) ≃ V)
    {i j : Fin (Fintype.card V)} (hij : i ≤ j) : chainPrefix σ i ⊆ chainPrefix σ j := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hij⟩

omit [DecidableEq V] in
lemma chainPrefix_terminal [DecidableEq V] (σ : Fin (Fintype.card V) ≃ V)
    (j : Fin (Fintype.card V)) (hj : ¬ (j : ℕ) + 1 < Fintype.card V) :
    chainPrefix σ j = Finset.univ := by
  ext v
  simp only [chainPrefix,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
  apply Fin.le_def.mpr
  have hv := (σ.symm v).isLt
  have hj' := j.isLt
  omega

omit [DecidableEq V] in
lemma indexed_prefix_sum [DecidableEq V] (σ : Fin (Fintype.card V) ≃ V)
    (j : Fin (Fintype.card V)) (x : V → ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => i ≤ j), x (σ i)) =
      ∑ v ∈ chainPrefix σ j, x v := by
  simp only [chainPrefix,Finset.sum_filter]
  simpa only [Equiv.symm_apply_apply] using
    σ.sum_comp (fun v => if σ.symm v ≤ j then x v else 0)

lemma pairing_chain_expansion (σ : Fin (Fintype.card V) ≃ V)
    (p : V → ℝ) (x : V → ℤ) :
    pairing p (toReal x) =
      ∑ j, chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ) := by
  have h := weighted_chain_expansion (p ∘ σ) (fun i => (x (σ i) : ℝ))
  rw [show (∑ i, (p ∘ σ) i * (x (σ i) : ℝ)) = pairing p (toReal x) from
    by simpa only [Function.comp_apply,pairing,toReal] using
      σ.sum_comp (fun v => p v * (x v : ℝ))] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [indexed_prefix_sum σ j (fun v => (x v : ℝ))]
  simp only [sumOn,Int.cast_sum]

lemma supportMin_satisfiesC1 [Nonempty V] (B : Finset (V → ℤ))
    (hB : IsIntegralBaseSet B) : SatisfiesC1 (supportMin B) := by
  obtain ⟨g,hg,hg0,hrep⟩ :=
    ((SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).2.1).mp hB
  have hcanon := (SteinitzExchange.Duality.baseSet_iff_submodular_system B hB.1).2.2.2
    g hg hg0 hrep
  have hval (X : Finset V) : supportMin B (charVec X) = (g X : ℝ) := by
    rw [hcanon X]
    exact supportMin_charVec B hB.1 X
  intro X Y
  change supportMin B (charVec X) + supportMin B (charVec Y) ≤
    supportMin B (charVec (X ∪ Y)) + supportMin B (charVec (X ∩ Y))
  rw [hval X,hval Y,hval (X ∪ Y),hval (X ∩ Y)]
  exact_mod_cast hg X Y

lemma supportMin_satisfiesC2 [Nonempty V] (B : Finset (V → ℤ))
    (hB : IsIntegralBaseSet B) : SatisfiesC2 (supportMin B) := by
  classical
  intro p σ hp
  let C := Finset.univ.image (chainPrefix σ)
  have hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hU
    rcases le_total i j with hij | hji
    · exact Or.inl (chainPrefix_mono σ hij)
    · exact Or.inr (chainPrefix_mono σ hji)
  obtain ⟨x,hx,hmin⟩ := chain_sum_minimizers hB C hchain
  have hprefix (j : Fin (Fintype.card V)) (y : V → ℤ) (hy : y ∈ B) :
      sumOn x (chainPrefix σ j) ≤ sumOn y (chainPrefix σ j) :=
    hmin _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) y hy
  have hxopt : ∀ y ∈ B, pairing p (toReal x) ≤ pairing p (toReal y) := by
    intro y hy
    rw [pairing_chain_expansion σ p x,pairing_chain_expansion σ p y]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hnext : (j : ℕ) + 1 < Fintype.card V
    · have hcoeff : 0 ≤ chainCoefficient (p ∘ σ) j := by
        rw [chainCoefficient,dif_pos hnext]
        exact sub_nonneg.mpr (hp (show j ≤ ⟨(j : ℕ) + 1,hnext⟩ from
          Fin.le_def.mpr (Nat.le_succ _)))
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hprefix j y hy) hcoeff
    · rw [chainPrefix_terminal σ j hnext]
      have ht : sumOn x Finset.univ = sumOn y Finset.univ :=
        SteinitzLocalRepairChain.base_sum_eq hB hx hy
      rw [ht]
  have hchar (j : Fin (Fintype.card V)) :
      supportMin B (charVec (chainPrefix σ j)) = (sumOn x (chainPrefix σ j) : ℝ) := by
    rw [← pairing_charVec]
    apply supportMin_eq_of_minimum B _ hx
    intro y hy
    simp only [pairing_charVec]
    exact_mod_cast hprefix j y hy
  rw [supportMin_eq_of_minimum B p hx hxopt,pairing_chain_expansion σ p x]
  change (∑ j, chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ)) =
    ∑ j, chainCoefficient (p ∘ σ) j * supportMin B (charVec (chainPrefix σ j))
  simp_rw [hchar]

theorem base_implies_support_matroidal [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) : IsMatroidal (supportMin B) :=
  ⟨supportMin_posHomogeneous B hB.1, supportMin_satisfiesC1 B hB, supportMin_satisfiesC2 B hB⟩


end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzSortedIndexing.lean -/
section

set_option autoImplicit false

namespace SteinitzLocalRepair

/-- A descending indexing, including ties, for a finite real-valued vector. -/
theorem exists_antitone_indexing {V : Type*} [Fintype V] (p : V → ℝ) :
    ∃ σ : Fin (Fintype.card V) ≃ V, Antitone (p ∘ σ) := by
  classical
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let f : Fin (Fintype.card V) → ℝᵒᵈ := fun i => OrderDual.toDual (p (e i))
  refine ⟨(Tuple.sort f).trans e, ?_⟩
  change Monotone (f ∘ Tuple.sort f)
  exact Tuple.monotone_sort f


end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalSupportConverse.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair
open SteinitzExchange.LocalSupermod
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
lemma linear_map_coordinates [Nonempty V] (f : (V → ℝ) →ₗ[ℝ] ℝ) (z : V → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : V → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
  calc
    f z = f (∑ i, z i • (Pi.single i 1 : V → ℝ)) := congrArg f hz
    _ = ∑ i, f (Pi.single i 1) * z i := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- All lower support inequalities characterize the finite convex hull. -/
theorem mem_hull_of_support_bounds (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (z : V → ℝ) (hs : ∀ p : V → ℝ, supportMin B p ≤ pairing p z) :
    z ∈ hull B := by
  by_contra hnot
  have hfinite : (toReal '' (B : Set (V → ℤ))).Finite :=
    (Finset.finite_toSet B).image toReal
  have hclosed : IsClosed (hull B) := hfinite.isClosed_convexHull ℝ
  have hconv : Convex ℝ (hull B) := convex_convexHull ℝ _
  obtain ⟨f,r,hfr,hrz⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
  let c : V → ℝ := fun i => -f (Pi.single i 1)
  have hc (y : V → ℝ) : pairing c y = -f y := by
    change (∑ i, (-f (Pi.single i 1)) * y i) = -f.toLinearMap y
    rw [linear_map_coordinates f.toLinearMap y]
    simp only [neg_mul, Finset.sum_neg_distrib, ContinuousLinearMap.coe_coe]
  have hlo : -r ≤ supportMin B c := by
    apply le_supportMin B hne c (-r)
    intro x hx
    have hxH : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x,hx,rfl⟩
    have hfx := hfr (toReal x) hxH
    rw [hc]
    exact neg_le_neg hfx.le
  have hp := hs c
  rw [hc] at hp
  linarith

omit [DecidableEq V] [Nonempty V] in
lemma pairing_constant [DecidableEq V] [Nonempty V] (t : ℝ) (x : V → ℤ) :
    pairing (fun _ => t) (toReal x) = t * (sumOn x Finset.univ : ℝ) := by
  simp [pairing, toReal, sumOn, Finset.mul_sum]

/-- C2 at a constant vector has only its terminal chain coefficient. -/
lemma c2_constant_value (h : (V → ℝ) → ℝ) (hc2 : SatisfiesC2 h) (t : ℝ) :
    h (fun _ => t) = t * h (charVec (Finset.univ : Finset V)) := by
  classical
  let σ : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  have hn : 0 < Fintype.card V := Fintype.card_pos
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hlast : ¬ (last : ℕ) + 1 < Fintype.card V := by
    dsimp [last]
    omega
  have hprefix : Finset.univ.filter (fun v : V => σ.symm v ≤ last) = Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hv := (σ.symm v).isLt
    change (σ.symm v).val ≤ Fintype.card V - 1
    omega
  have hs := hc2 (fun _ => t) σ (fun _ _ _ => le_rfl)
  change h (fun _ => t) = ∑ j : Fin (Fintype.card V),
    (t - (if hj : (j : ℕ) + 1 < Fintype.card V then t else 0)) *
      h (charVec (Finset.univ.filter (fun v : V => σ.symm v ≤ j))) at hs
  rw [hs, Finset.sum_eq_single last]
  · simp only [dif_neg hlast, sub_zero, hprefix]
  · intro j hj hne
    have hjnext : (j : ℕ) + 1 < Fintype.card V := by
      by_contra h
      have hjlt := j.isLt
      have he : (j : ℕ) = Fintype.card V - 1 := by omega
      apply hne
      apply Fin.ext
      exact he
    simp only [dif_pos hjnext, sub_self, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ last)).elim

/-- The negative constant test forces every member to have the minimum total. -/
lemma c2_common_total (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hc2 : SatisfiesC2 (supportMin B)) (x : V → ℤ) (hx : x ∈ B) :
    sumOn x Finset.univ = B.inf' hne (fun y => sumOn y Finset.univ) := by
  have hconst := c2_constant_value (supportMin B) hc2 (-1)
  have h := supportMin_le_pairing B (fun _ => -1) hx
  rw [hconst, pairing_constant, supportMin_charVec B hne] at h
  have hreal : (sumOn x Finset.univ : ℝ) ≤
      ((B.inf' hne (fun y => sumOn y Finset.univ) : ℤ) : ℝ) := by linarith
  apply le_antisymm
  · exact_mod_cast hreal
  · exact B.inf'_le (fun y => sumOn y Finset.univ) hx

end SteinitzLocalRepair
end

/- Component: Solutions/SteinitzLocalConverse.lean -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SteinitzLocalRepair
open SteinitzExchange.LocalSupermod
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- With the required lattice saturation, C1 and C2 recover a supermodular base system. -/
theorem support_matroidal_implies_base (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ x : V → ℤ, toReal x ∈ hull B → x ∈ B)
    (hm : IsMatroidal (supportMin B)) : IsIntegralBaseSet B := by
  classical
  let g : Finset V → ℤ := fun X => B.inf' hne (fun x => sumOn x X)
  have hg0 : g ∅ = 0 := by simp [g, sumOn]
  have hg : IsSupermodular g := by
    intro X Y
    have h := hm.2.1 X Y
    change supportMin B (charVec X) + supportMin B (charVec Y) ≤
      supportMin B (charVec (X ∪ Y)) + supportMin B (charVec (X ∩ Y)) at h
    simp_rw [supportMin_charVec B hne] at h
    dsimp only [g]
    exact_mod_cast h
  have hlower (x : V → ℤ) (hx : x ∈ B) (X : Finset V) : g X ≤ sumOn x X :=
    B.inf'_le (fun y => sumOn y X) hx
  have htotal (x : V → ℤ) (hx : x ∈ B) : sumOn x Finset.univ = g Finset.univ :=
    c2_common_total B hne hm.2.2 x hx
  have hrep : ∀ x : V → ℤ, x ∈ B ↔
      (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ := by
    intro x
    constructor
    · intro hx
      exact ⟨hlower x hx, htotal x hx⟩
    · intro hx
      apply hconv x
      apply mem_hull_of_support_bounds B hne (toReal x)
      intro p
      obtain ⟨σ,hp⟩ := exists_antitone_indexing p
      have hc2 := hm.2.2 p σ hp
      change supportMin B p = ∑ j,
        chainCoefficient (p ∘ σ) j * supportMin B (charVec (chainPrefix σ j)) at hc2
      rw [hc2, pairing_chain_expansion σ p x]
      apply Finset.sum_le_sum
      intro j hj
      rw [supportMin_charVec B hne]
      change chainCoefficient (p ∘ σ) j * (g (chainPrefix σ j) : ℝ) ≤
        chainCoefficient (p ∘ σ) j * (sumOn x (chainPrefix σ j) : ℝ)
      by_cases hnext : (j : ℕ) + 1 < Fintype.card V
      · have hcoeff : 0 ≤ chainCoefficient (p ∘ σ) j := by
          rw [chainCoefficient, dif_pos hnext]
          exact sub_nonneg.mpr (hp (show j ≤ ⟨(j : ℕ) + 1,hnext⟩ from
            Fin.le_def.mpr (Nat.le_succ _)))
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hx.1 (chainPrefix σ j)) hcoeff
      · have he : (g (chainPrefix σ j) : ℝ) = (sumOn x (chainPrefix σ j) : ℝ) := by
          rw [chainPrefix_terminal σ j hnext, hx.2]
        exact le_of_eq (congrArg (fun t : ℝ => chainCoefficient (p ∘ σ) j * t) he)
  exact (SteinitzExchange.Duality.baseSet_iff_submodular_system B hne).2.1.mpr
    ⟨g,hg,hg0,hrep⟩

/-- The lattice-saturation premise is retained exactly in both directions. -/
theorem base_iff_support_matroidal_complete (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ x : V → ℤ, toReal x ∈ hull B → x ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) :=
  ⟨base_implies_support_matroidal B, support_matroidal_implies_base B hne hconv⟩

end SteinitzLocalRepair
end

section
open SteinitzExchange.LocalSupermod

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) :=
  SteinitzLocalRepair.base_iff_support_matroidal_complete B hne hconv

end

end AttributedSteinitz.Support

section
open SteinitzExchange.LocalSupermod
theorem checked_baseSet_iff_support_matroidal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B) :
    IsIntegralBaseSet B ↔ IsMatroidal (supportMin B) := by
  exact AttributedSteinitz.Support.solution B hne hconv
end


namespace AttributedSteinitz.Closure
-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.concaveClosure_eq_of_exc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:19:30.210955+00:00
-- url     : https://prove2.me/submissions/1a415219-415d-43b9-9bd9-a94c3a1e7e86


set_option autoImplicit false

namespace Sol2f8a2c6e

open SteinitzExchange.LocalSupermod

/-! ## S1.0 Linear algebra of `pairing` and `toReal` -/

theorem murota_pairing_add_right {V : Type*} [Fintype V] (p b c : V → ℝ) :
    pairing p (b + c) = pairing p b + pairing p c := by
  simp only [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem murota_pairing_smul_right {V : Type*} [Fintype V] (p b : V → ℝ) (a : ℝ) :
    pairing p (a • b) = a * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem murota_pairing_smul_left {V : Type*} [Fintype V] (p b : V → ℝ) (a : ℝ) :
    pairing (a • p) b = a * pairing p b := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem murota_pairing_add_left {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p + q) b = pairing p b + pairing q b := by
  simp only [pairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem murota_pairing_sub_left {V : Type*} [Fintype V] (p q b : V → ℝ) :
    pairing (p - q) b = pairing p b - pairing q b := by
  simp only [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem murota_pairing_zero_left {V : Type*} [Fintype V] (b : V → ℝ) :
    pairing 0 b = 0 := by
  simp only [pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-! ## S1.1 The concave conjugate and the closure family -/

theorem murota_concaveConj_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (p : V → ℝ) {x : V → ℤ} (hx : x ∈ B) :
    concaveConj B g p ≤ pairing p (toReal x) - g x := by
  unfold concaveConj
  have : Finite (B : Set (V → ℤ)) := B.finite_toSet.to_subtype
  have hbdd : BddBelow (Set.range fun y : (B : Set (V → ℤ)) =>
      pairing p (toReal (y : V → ℤ)) - g y) := (Set.finite_range _).bddBelow
  exact ciInf_le hbdd (⟨x, hx⟩ : (B : Set (V → ℤ)))

theorem murota_exists_concaveConj_eq {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) :
    ∃ x ∈ B, concaveConj B g p = pairing p (toReal x) - g x := by
  unfold concaveConj
  have : Finite (B : Set (V → ℤ)) := B.finite_toSet.to_subtype
  have : Nonempty (B : Set (V → ℤ)) := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨⟨x, hx⟩, hxe⟩ := exists_eq_ciInf_of_finite
    (f := fun y : (B : Set (V → ℤ)) => pairing p (toReal (y : V → ℤ)) - g y)
  exact ⟨x, hx, hxe.symm⟩

/-- Every member of the closure family is `≥ c` on `B̄` when `c ≤ g` on `B`. -/
theorem murota_family_ge_of_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (c : ℝ) (hc : ∀ x ∈ B, c ≤ g x) (p : V → ℝ) {b : V → ℝ}
    (hb : b ∈ hull B) : c ≤ pairing p b - concaveConj B g p := by
  set k := concaveConj B g p with hk
  have hsub : toReal '' (B : Set (V → ℤ)) ⊆ {b | c ≤ pairing p b - k} := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := murota_concaveConj_le B g p (Finset.mem_coe.mp hx)
    have h2 := hc x (Finset.mem_coe.mp hx)
    show c ≤ pairing p (toReal x) - k
    linarith
  have hconv : Convex ℝ {b | c ≤ pairing p b - k} := by
    intro x hx y hy a t ha ht hat
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [murota_pairing_add_right, murota_pairing_smul_right, murota_pairing_smul_right]
    have e1 : a * c + t * c = c := by rw [← add_mul, hat, one_mul]
    have e2 : a * k + t * k = k := by rw [← add_mul, hat, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy ht]
  exact convexHull_min hsub hconv hb

theorem murota_bddBelow_family {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) {b : V → ℝ} (hb : b ∈ hull B) :
    BddBelow (Set.range fun p : V → ℝ => pairing p b - concaveConj B g p) := by
  obtain ⟨x0, hx0, hmin⟩ := B.exists_min_image g hB
  refine ⟨g x0, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact murota_family_ge_of_le B g (g x0) hmin p hb

theorem murota_concaveClosure_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) {b : V → ℝ} (hb : b ∈ hull B) (p : V → ℝ) :
    concaveClosure B g b ≤ pairing p b - concaveConj B g p :=
  ciInf_le (murota_bddBelow_family B hB g hb) p

/-! ## S1.3 Deliverable (b): the closure majorises `g` on `B`; and `ĝ ≤ max g` on `B̄` -/

theorem murota_le_concaveClosure {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) {x : V → ℤ} (hx : x ∈ B) :
    g x ≤ concaveClosure B g (toReal x) := by
  unfold concaveClosure
  refine le_ciInf fun p => ?_
  have := murota_concaveConj_le B g p hx
  linarith

theorem murota_concaveClosure_le_of_le {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (M : ℝ) (hM : ∀ x ∈ B, g x ≤ M)
    {b : V → ℝ} (hb : b ∈ hull B) : concaveClosure B g b ≤ M := by
  have h := murota_concaveClosure_le B hB g hb 0
  obtain ⟨x, hx, hxe⟩ := murota_exists_concaveConj_eq B hB g 0
  rw [hxe, murota_pairing_zero_left, murota_pairing_zero_left] at h
  have := hM x hx
  linarith

/-! ## S1.4 Deliverable (c): under (EXC), `argmax(ω[p])` is an integral base set -/

theorem murota_perturb_exchange_sum {V : Type*} [Fintype V] [DecidableEq V]
    (ω : (V → ℤ) → ℝ) (p : V → ℝ) (x y : V → ℤ) (u v : V) :
    perturb ω p (x - chi u + chi v) + perturb ω p (y + chi u - chi v) =
      ω (x - chi u + chi v) + ω (y + chi u - chi v) + (pairing p (toReal x) + pairing p (toReal y)) := by
  unfold perturb
  have : pairing p (toReal (x - chi u + chi v)) + pairing p (toReal (y + chi u - chi v)) =
      pairing p (toReal x) + pairing p (toReal y) := by
    rw [← murota_pairing_add_right, ← murota_pairing_add_right]
    congr 1
    funext w
    simp only [toReal, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
    ring
  linarith

/-! ## S1.6 Deliverable (e): potentials for a digraph with no positive cycle

A walk is a vertex list `L` with `L.IsChain adj`; its weight is `murotaWalkWeight w L`
(sum of `w a b` over consecutive pairs). A closed walk is one with `L.head? = L.getLast?`. -/

/-- Weight of a walk given by its vertex list. -/
def murotaWalkWeight {V : Type*} (w : V → V → ℝ) : List V → ℝ
  | a :: b :: l => w a b + murotaWalkWeight w (b :: l)
  | _ => 0

theorem murotaWalkWeight_nil {V : Type*} (w : V → V → ℝ) : murotaWalkWeight w [] = 0 := rfl

theorem murotaWalkWeight_single {V : Type*} (w : V → V → ℝ) (a : V) :
    murotaWalkWeight w [a] = 0 := rfl

theorem murotaWalkWeight_cons_cons {V : Type*} (w : V → V → ℝ) (a b : V) (l : List V) :
    murotaWalkWeight w (a :: b :: l) = w a b + murotaWalkWeight w (b :: l) := rfl

theorem murotaWalkWeight_append {V : Type*} (w : V → V → ℝ) (x : V) (l₂ : List V) :
    ∀ l₁ : List V, murotaWalkWeight w (l₁ ++ x :: l₂) =
      murotaWalkWeight w (l₁ ++ [x]) + murotaWalkWeight w (x :: l₂)
  | [] => by simp [murotaWalkWeight_single]
  | [a] => by simp [murotaWalkWeight_cons_cons, murotaWalkWeight_single]
  | a :: b :: l₁ => by
    have ih := murotaWalkWeight_append w x l₂ (b :: l₁)
    simp only [List.cons_append] at ih ⊢
    rw [murotaWalkWeight_cons_cons, murotaWalkWeight_cons_cons, ih]
    ring

theorem murotaWalkWeight_le {V : Type*} (w : V → V → ℝ) (K : ℝ) (hK : ∀ a b, w a b ≤ K)
    (hK0 : 0 ≤ K) : ∀ l : List V, murotaWalkWeight w l ≤ l.length * K
  | [] => by simp [murotaWalkWeight_nil]
  | [a] => by simp [murotaWalkWeight_single]; exact hK0
  | a :: b :: l => by
    have ih := murotaWalkWeight_le w K hK hK0 (b :: l)
    rw [murotaWalkWeight_cons_cons]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith [hK a b]

theorem murota_exists_split_of_not_nodup {V : Type*} {x : V} :
    ∀ L : List V, [x, x].Sublist L → ∃ a b c : List V, L = a ++ x :: (b ++ x :: c)
  | [], h => by simp at h
  | y :: L, h => by
    rcases List.sublist_cons_iff.mp h with h' | ⟨r, hr, h'⟩
    · obtain ⟨a, b, c, rfl⟩ := murota_exists_split_of_not_nodup L h'
      exact ⟨y :: a, b, c, by simp⟩
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨b, c, rfl⟩ := List.append_of_mem (List.singleton_sublist.mp h')
      exact ⟨[], b, c, by simp⟩

/-- Cycle removal: every walk is dominated by a simple walk with the same last vertex. -/
theorem murota_exists_nodup_walk {V : Type*} (adj : V → V → Prop) (w : V → V → ℝ)
    (hcyc : ∀ L : List V, L.IsChain adj → L.head? = L.getLast? → murotaWalkWeight w L ≤ 0) :
    ∀ n : ℕ, ∀ L : List V, L.length ≤ n → L.IsChain adj →
      ∃ L' : List V, L'.IsChain adj ∧ L'.getLast? = L.getLast? ∧ L'.Nodup ∧
        murotaWalkWeight w L ≤ murotaWalkWeight w L' := by
  intro n
  induction n with
  | zero =>
    intro L hL hc
    have : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hL)
    subst this
    exact ⟨[], hc, rfl, List.nodup_nil, le_rfl⟩
  | succ n ih =>
    intro L hL hc
    by_cases hnd : L.Nodup
    · exact ⟨L, hc, rfl, hnd, le_rfl⟩
    rw [List.nodup_iff_sublist] at hnd
    simp only [not_forall, not_not] at hnd
    obtain ⟨x, hx⟩ := hnd
    obtain ⟨a, b, c, rfl⟩ := murota_exists_split_of_not_nodup _ hx
    -- the shortcut walk
    have hc' := hc
    rw [List.isChain_append] at hc'
    obtain ⟨hca, hcx, hlink⟩ := hc'
    have hcxc : (x :: c).IsChain adj := hcx.suffix ⟨x :: b, by simp⟩
    have hcyc_chain : (x :: (b ++ [x])).IsChain adj := hcx.infix ⟨[], c, by simp⟩
    have hshort : (a ++ x :: c).IsChain adj :=
      List.isChain_append.mpr ⟨hca, hcxc, by simpa using hlink⟩
    have hlen : (a ++ x :: c).length ≤ n := by
      simp only [List.length_append, List.length_cons] at hL ⊢
      omega
    obtain ⟨L', hL'c, hL'last, hL'nd, hL'w⟩ := ih _ hlen hshort
    have hlast : (x :: (b ++ x :: c)).getLast? = (x :: c).getLast? := by
      rw [List.getLast?_cons, List.getLast?_append, List.getLast?_cons]
      rfl
    refine ⟨L', hL'c, ?_, hL'nd, ?_⟩
    · rw [hL'last, List.getLast?_append, List.getLast?_append, hlast]
    · have hcycw := hcyc _ hcyc_chain (by rw [← List.cons_append, List.getLast?_concat]; rfl)
      have e1 := murotaWalkWeight_append w x (b ++ x :: c) a
      have e2 := murotaWalkWeight_append w x c (x :: b)
      have e3 := murotaWalkWeight_append w x c a
      simp only [List.cons_append] at e2
      linarith

theorem murota_exists_potential {V : Type*} [Fintype V] (adj : V → V → Prop) (w : V → V → ℝ)
    (hcyc : ∀ L : List V, L.IsChain adj → L.head? = L.getLast? → murotaWalkWeight w L ≤ 0) :
    ∃ p : V → ℝ, ∀ u v, adj u v → w u v ≤ p v - p u := by
  classical
  set K : ℝ := ∑ a, ∑ b, |w a b| with hKdef
  have hK : ∀ a b, w a b ≤ K := by
    intro a b
    refine (le_abs_self _).trans ?_
    calc |w a b| ≤ ∑ b', |w a b'| :=
          Finset.single_le_sum (f := fun b' => |w a b'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
      _ ≤ K := Finset.single_le_sum (f := fun a' => ∑ b', |w a' b'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  let S : V → Set ℝ := fun v =>
    {r | ∃ L : List V, L.IsChain adj ∧ L.getLast? = some v ∧ murotaWalkWeight w L = r}
  have hne : ∀ v, (S v).Nonempty := fun v => ⟨0, [v], List.isChain_singleton v, rfl, rfl⟩
  have hbdd : ∀ v, BddAbove (S v) := by
    intro v
    refine ⟨(Fintype.card V : ℝ) * K, ?_⟩
    rintro _ ⟨L, hLc, _, rfl⟩
    obtain ⟨L', _, _, hnd, hle⟩ := murota_exists_nodup_walk adj w hcyc L.length L le_rfl hLc
    have h1 := murotaWalkWeight_le w K hK hK0 L'
    have h2 : (L'.length : ℝ) ≤ Fintype.card V := by exact_mod_cast hnd.length_le_card
    nlinarith
  refine ⟨fun v => sSup (S v), fun u v huv => ?_⟩
  have key : sSup (S u) ≤ sSup (S v) - w u v := by
    refine csSup_le (hne u) ?_
    rintro _ ⟨L, hLc, hLl, rfl⟩
    obtain ⟨L0, rfl⟩ := List.getLast?_eq_some_iff.mp hLl
    have hmem : murotaWalkWeight w ((L0 ++ [u]) ++ [v]) ∈ S v := by
      refine ⟨(L0 ++ [u]) ++ [v], ?_, by simp, rfl⟩
      exact List.isChain_append.mpr ⟨hLc, List.isChain_singleton v, by simpa using huv⟩
    have hw : murotaWalkWeight w ((L0 ++ [u]) ++ [v]) = murotaWalkWeight w (L0 ++ [u]) + w u v := by
      rw [List.append_assoc, List.singleton_append, murotaWalkWeight_append w u [v] L0,
        murotaWalkWeight_cons_cons, murotaWalkWeight_single]
      ring
    have := le_csSup (hbdd v) hmem
    linarith
  show w u v ≤ sSup (S v) - sSup (S u)
  linarith

/-! ## S2 Lemma 4.5: under (EXC) there is a supergradient at every point of `B`

Route (Murota 1996, Lemma 4.5):
1. `murota_local_opt`: local optimality by induction on the l1 distance.
2. `murota_exc_triangle`: in the exchange graph at `x` (arcs `u → v` when `x − χ_u + χ_v ∈ B`,
   weight `ω(x − χ_u + χ_v) − ω x`) two consecutive arcs can be shortcut, weight not decreasing.
3. `murota_exc_no_positive_cycle`: hence every closed walk has weight `≤ 0`.
4. `murota_exists_potential` (S1) gives potentials; local optimality of `ω[−p]` at `x`
   gives the supergradient `murota_exists_supergradient`. -/

/-! ### S2.0 Linear algebra of `toReal`, `chi` and `pairing` -/

theorem murota_pairing_sub_right {V : Type*} [Fintype V] (p b c : V → ℝ) :
    pairing p (b - c) = pairing p b - pairing p c := by
  simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem murota_pairing_neg_left {V : Type*} [Fintype V] (p b : V → ℝ) :
    pairing (-p) b = -pairing p b := by
  simp only [pairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem murota_toReal_add {V : Type*} (a b : V → ℤ) : toReal (a + b) = toReal a + toReal b := by
  funext w
  simp only [toReal, Pi.add_apply, Int.cast_add]

theorem murota_toReal_sub {V : Type*} (a b : V → ℤ) : toReal (a - b) = toReal a - toReal b := by
  funext w
  simp only [toReal, Pi.sub_apply, Int.cast_sub]

theorem murota_pairing_toReal_chi {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (u : V) :
    pairing p (toReal (chi u)) = p u := by
  unfold pairing
  rw [Finset.sum_eq_single u]
  · simp [toReal, chi]
  · intro b _ hb
    simp [toReal, chi, hb]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- `⟨p, x − χ_u + χ_v⟩ = ⟨p, x⟩ − p u + p v`. -/
theorem murota_pairing_toReal_exchange {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ)
    (x : V → ℤ) (u v : V) :
    pairing p (toReal (x - chi u + chi v)) = pairing p (toReal x) - p u + p v := by
  rw [murota_toReal_add, murota_toReal_sub, murota_pairing_add_right, murota_pairing_sub_right,
    murota_pairing_toReal_chi, murota_pairing_toReal_chi]

/-! ### S2.1 (EXC) is preserved by linear perturbation -/

theorem murota_perturb_satisfiesEXC {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) (p : V → ℝ) :
    SatisfiesEXC B (perturb ω p) := by
  intro x hx y hy u hu
  obtain ⟨v, hv, h1, h2, hle⟩ := hω x hx y hy u hu
  refine ⟨v, hv, h1, h2, ?_⟩
  have key := murota_perturb_exchange_sum ω p x y u v
  have e : perturb ω p x + perturb ω p y =
      ω x + ω y + (pairing p (toReal x) + pairing p (toReal y)) := by
    unfold perturb
    ring
  linarith

/-! ### S2.2 Local optimality (induction on the l1 distance) -/

/-- Under (EXC), two distinct points of `B` have `supp⁺(x − y) ≠ ∅`. -/
theorem murota_exists_pos_of_ne {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x y : V → ℤ} (hx : x ∈ B) (hy : y ∈ B)
    (hne : y ≠ x) : ∃ u : V, 0 < (x - y) u := by
  by_contra h
  simp only [not_exists, not_lt] at h
  obtain ⟨u, hu⟩ := Function.ne_iff.mp hne
  have h1 : 0 < (y - x) u := by
    have := h u
    simp only [Pi.sub_apply] at this ⊢
    omega
  obtain ⟨v, hv, -⟩ := hω y hy x hx u h1
  have := h v
  simp only [Pi.sub_apply] at this hv
  omega

/-- The exchange `y ↦ y + χ_u − χ_v` with `u ∈ supp⁺(x − y)`, `v ∈ supp⁻(x − y)` moves `y`
strictly closer to `x` in the l1 distance. -/
theorem murota_l1_exchange_lt {V : Type*} [Fintype V] [DecidableEq V] (x y : V → ℤ) (u v : V)
    (hu : 0 < (x - y) u) (hv : (x - y) v < 0) :
    ∑ w, (x w - (y + chi u - chi v) w).natAbs < ∑ w, (x w - y w).natAbs := by
  simp only [Pi.sub_apply] at hu hv
  have huv : u ≠ v := by
    rintro rfl
    omega
  apply Finset.sum_lt_sum
  · intro w _
    simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> omega
  · refine ⟨u, Finset.mem_univ _, ?_⟩
    have e : (y + chi u - chi v) u = y u + 1 := by simp [chi, huv]
    rw [e]
    omega

/-- Local optimality (Murota 1996, Theorem 2.? / Lemma 4.5 step 1): under (EXC), a point of `B`
that is not improved by any single exchange `x − χ_u + χ_v` is a global maximiser on `B`. -/
theorem murota_local_opt {V : Type*} [Fintype V] [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B)
    (hloc : ∀ u v : V, x - chi u + chi v ∈ B → ω (x - chi u + chi v) ≤ ω x) :
    ∀ y ∈ B, ω y ≤ ω x := by
  suffices H : ∀ n : ℕ, ∀ y ∈ B, ∑ w, (x w - y w).natAbs < n → ω y ≤ ω x from
    fun y hy => H _ y hy (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro y _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro y hy hn
    by_cases hyx : y = x
    · rw [hyx]
    obtain ⟨u, hu⟩ := murota_exists_pos_of_ne B ω hω hx hy hyx
    obtain ⟨v, hv, hx', hy', hle⟩ := hω x hx y hy u hu
    have h1 := hloc u v hx'
    have hlt := murota_l1_exchange_lt x y u v hu hv
    have h2 := ih (y + chi u - chi v) hy' (by omega)
    linarith

/-! ### S2.3 The exchange graph at `x` has no positive cycle -/

/-- Shortcut of two consecutive arcs `a → b → c` of the exchange graph at `x`. -/
theorem murota_exc_triangle {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (a b c : V)
    (hab : x - chi a + chi b ∈ B) (hbc : x - chi b + chi c ∈ B) :
    x - chi a + chi c ∈ B ∧
      ω (x - chi a + chi b) + ω (x - chi b + chi c) ≤ ω x + ω (x - chi a + chi c) := by
  by_cases hba : b = a
  · subst hba
    simp only [sub_add_cancel]
    exact ⟨hbc, le_refl _⟩
  by_cases hbc' : b = c
  · subst hbc'
    simp only [sub_add_cancel]
    exact ⟨hab, by linarith⟩
  have hpos : 0 < (x - chi a + chi b - (x - chi b + chi c)) b := by
    have e : (x - chi a + chi b - (x - chi b + chi c)) b = 2 := by simp [chi, hba, hbc']
    omega
  obtain ⟨v, hv, hm1, hm2, hle⟩ := hω _ hab _ hbc b hpos
  have hv' : v = a ∨ v = c := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hva, hvc⟩ := hcon
    simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply, if_neg hva, if_neg hvc] at hv
    split_ifs at hv <;> omega
  rcases hv' with h | h
  · rw [h] at hm1 hm2 hle
    have e1 : x - chi a + chi b - chi b + chi a = x := by abel
    have e2 : x - chi b + chi c + chi b - chi a = x - chi a + chi c := by abel
    rw [e1, e2] at hle
    rw [e2] at hm2
    exact ⟨hm2, hle⟩
  · rw [h] at hm1 hm2 hle
    have e1 : x - chi a + chi b - chi b + chi c = x - chi a + chi c := by abel
    have e2 : x - chi b + chi c + chi b - chi c = x := by abel
    rw [e1, e2] at hle
    rw [e1] at hm1
    exact ⟨hm1, by linarith⟩

/-- A walk `a → ⋯ → b` in the exchange graph at `x` is dominated by the single arc `a → b`. -/
theorem murota_exc_walk_le {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∀ (L : List V) (a b : V), (a :: L).IsChain (fun u v => x - chi u + chi v ∈ B) →
      (a :: L).getLast? = some b →
      x - chi a + chi b ∈ B ∧
        murotaWalkWeight (fun u v => ω (x - chi u + chi v) - ω x) (a :: L) ≤
          ω (x - chi a + chi b) - ω x
  | [], a, b, _, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    rw [murotaWalkWeight_single, sub_add_cancel]
    exact ⟨hx, le_of_eq (sub_self _).symm⟩
  | c :: L, a, b, hc, hl => by
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at hl
    obtain ⟨h1, h2⟩ := murota_exc_walk_le B ω hω hx L c b hc.2 hl
    obtain ⟨h3, h4⟩ := murota_exc_triangle B ω hω a c b hc.1 h1
    refine ⟨h3, ?_⟩
    rw [murotaWalkWeight_cons_cons]
    linarith

/-- The cycle inequality: every closed walk of the exchange graph at `x` has weight `≤ 0`. -/
theorem murota_exc_no_positive_cycle {V : Type*} [DecidableEq V] (B : Finset (V → ℤ))
    (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∀ L : List V, L.IsChain (fun u v => x - chi u + chi v ∈ B) → L.head? = L.getLast? →
      murotaWalkWeight (fun u v => ω (x - chi u + chi v) - ω x) L ≤ 0
  | [], _, _ => le_of_eq (murotaWalkWeight_nil _)
  | a :: L, hc, hl => by
    have hl' : (a :: L).getLast? = some a := by rw [← hl]; rfl
    have h := (murota_exc_walk_le B ω hω hx L a a hc hl').2
    rw [sub_add_cancel, sub_self] at h
    exact h

/-! ### S2.4 Deliverable: Lemma 4.5 (supergradient at every point of `B`) -/

/-- **Murota 1996, Lemma 4.5.** Under (EXC), every `x ∈ B` has a supergradient `p`:
`ω y ≤ ω x + ⟨p, y − x⟩` for all `y ∈ B`. -/
theorem murota_exists_supergradient {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∃ p : V → ℝ, ∀ y ∈ B, ω y ≤ ω x + pairing p (toReal y - toReal x) := by
  obtain ⟨p, hp⟩ := murota_exists_potential (fun u v => x - chi u + chi v ∈ B)
    (fun u v => ω (x - chi u + chi v) - ω x) (murota_exc_no_positive_cycle B ω hω hx)
  refine ⟨p, fun y hy => ?_⟩
  have hloc : ∀ u v : V, x - chi u + chi v ∈ B →
      perturb ω (-p) (x - chi u + chi v) ≤ perturb ω (-p) x := by
    intro u v huv
    have h := hp u v huv
    unfold perturb
    rw [murota_pairing_toReal_exchange, Pi.neg_apply, Pi.neg_apply]
    linarith
  have key := murota_local_opt B (perturb ω (-p)) (murota_perturb_satisfiesEXC B ω hω (-p)) hx
    hloc y hy
  unfold perturb at key
  rw [murota_pairing_neg_left, murota_pairing_neg_left] at key
  rw [murota_pairing_sub_right]
  linarith

/-- Lemma 4.5, argmax form: every `x ∈ B` maximises some perturbation `ω[p]` on `B`. -/
theorem murota_mem_argmaxB_of_exc {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    ∃ p : V → ℝ, x ∈ argmaxB B (perturb ω p) := by
  obtain ⟨p, hp⟩ := murota_exists_supergradient B ω hω hx
  refine ⟨-p, ?_⟩
  rw [argmaxB, Finset.mem_filter]
  refine ⟨hx, fun y hy => ?_⟩
  have h := hp y hy
  unfold perturb
  rw [murota_pairing_neg_left, murota_pairing_neg_left]
  rw [murota_pairing_sub_right] at h
  linarith

/-- Consequence of Lemma 4.5: under (EXC) the concave closure agrees with `ω` on `B`. -/
theorem murota_concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω) {x : V → ℤ} (hx : x ∈ B) :
    concaveClosure B ω (toReal x) = ω x := by
  obtain ⟨p, hp⟩ := murota_exists_supergradient B ω hω hx
  have hB : B.Nonempty := ⟨x, hx⟩
  have hxhull : toReal x ∈ hull B := subset_convexHull ℝ _ ⟨x, Finset.mem_coe.mpr hx, rfl⟩
  refine le_antisymm ?_ (murota_le_concaveClosure B ω hx)
  have h1 := murota_concaveClosure_le B hB ω hxhull p
  obtain ⟨y, hy, hye⟩ := murota_exists_concaveConj_eq B hB ω p
  have h2 := hp y hy
  rw [murota_pairing_sub_right] at h2
  rw [hye] at h1
  linarith


end Sol2f8a2c6e

open SteinitzExchange.LocalSupermod in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (_hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by
  intro x hx
  exact Sol2f8a2c6e.murota_concaveClosure_eq_of_exc B ω hω hx

end AttributedSteinitz.Closure

section
open SteinitzExchange.LocalSupermod
theorem checked_concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by
  exact AttributedSteinitz.Closure.solution B hB ω hω
end


namespace AttributedSteinitz.Localization
-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.localization_eq_min_argmax
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:58:49.316333+00:00
-- url     : https://prove2.me/submissions/3e40f730-559e-4856-9464-a9d8f4c07f45

open Set
open SteinitzExchange.LocalSupermod

private theorem finite_affine_min {J : Type*} [Fintype J] [Nonempty J] (a b : J → ℝ) :
    ∃ (j : J) (t : ℝ),0<t ∧ (∀ k,a j ≤ a k) ∧
      (∀ k,a k=a j → b j ≤ b k) ∧ ∀ k,a j+t*b j ≤ a k+t*b k := by
  classical
  obtain ⟨j₀,hj₀,hmin⟩ := Finset.univ.exists_min_image a Finset.univ_nonempty
  let S := Finset.univ.filter (fun j => a j=a j₀)
  have hS : S.Nonempty := ⟨j₀,by simp [S]⟩
  obtain ⟨j,hj,hb⟩ := S.exists_min_image b hS
  have ha : a j=a j₀ := (Finset.mem_filter.mp hj).2
  have hminj (k : J) : a j ≤ a k := ha.symm ▸ hmin k (Finset.mem_univ _)
  have hbmin (k : J) (hk : a k=a j) : b j ≤ b k := hb k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.trans ha⟩)
  let e : J → ℝ := fun k => if a k=a j then 1 else (a k-a j)/(|b k-b j|+1)
  have hepos (k : J) : 0<e k := by
    dsimp [e]
    split_ifs with hk
    · norm_num
    · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hminj k) (Ne.symm hk))) (by positivity)
  let t := Finset.univ.inf' Finset.univ_nonempty e
  have ht : 0<t := (Finset.lt_inf'_iff _).mpr (fun k _ => hepos k)
  refine ⟨j,t,ht,hminj,hbmin,?_⟩
  intro k
  have htk : t ≤ e k := Finset.inf'_le _ (Finset.mem_univ k)
  by_cases hk : a k=a j
  · rw [hk]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hbmin k hk) ht.le)
  · simp only [e,if_neg hk] at htk
    have htk := (le_div_iff₀ (show 0 < |b k-b j|+1 by positivity)).mp htk
    have hab : b j-b k ≤ |b k-b j| := by rw [abs_sub_comm];exact le_abs_self _
    have hh := mul_le_mul_of_nonneg_left hab ht.le
    nlinarith only [htk,hh,ht]

private theorem pairing_add_left {V : Type*} [Fintype V] (p q z : V → ℝ) :
    pairing (p+q) z=pairing p z+pairing q z := by
  simp only [pairing,Pi.add_apply,add_mul,Finset.sum_add_distrib]

private theorem pairing_sub_left {V : Type*} [Fintype V] (p q z : V → ℝ) :
    pairing (p-q) z=pairing p z-pairing q z := by
  simp only [pairing,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]

private theorem pairing_smul_left {V : Type*} [Fintype V] (t : ℝ) (p z : V → ℝ) :
    pairing (t • p) z=t*pairing p z := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

private theorem perturb_neg {V : Type*} [Fintype V] (g : (V → ℤ) → ℝ) (p : V → ℝ) (x : V → ℤ) :
    perturb g (-p) x=-(pairing p (toReal x)-g x) := by
  simp [perturb,pairing,Finset.sum_neg_distrib]
  ring

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ p : V → ℝ) :
    IsLeast ((fun x => pairing p (toReal x)) '' (argmaxB B (perturb ω (-p₀)) : Set (V → ℤ)))
      (localization (concaveConj B ω) p₀ p) := by
  classical
  have : Nonempty (B : Set (V → ℤ)) := by obtain ⟨x,hx⟩:=hB.1;exact ⟨⟨x,hx⟩⟩
  let a : ↥(B : Set (V → ℤ)) → ℝ := fun x => pairing p₀ (toReal (x : V → ℤ))-ω x
  let b : ↥(B : Set (V → ℤ)) → ℝ := fun x => pairing p (toReal (x : V → ℤ))
  obtain ⟨x,t,ht,hmin,hbmin,htmin⟩ := finite_affine_min a b
  have h0 : concaveConj B ω p₀=a x := le_antisymm (ciInf_le (Set.finite_range a).bddBelow x) (le_ciInf hmin)
  have ht0 : concaveConj B ω (p₀+t • p)=a x+t*b x := by
    have hf (y : (B : Set (V → ℤ))) : pairing (p₀+t • p) (toReal (y : V → ℤ))-ω y=a y+t*b y := by
      rw [pairing_add_left,pairing_smul_left]
      dsimp [a,b]
      ring
    unfold concaveConj
    simp only [hf]
    exact le_antisymm (ciInf_le (Set.finite_range (fun y => a y+t*b y)).bddBelow x) (le_ciInf htmin)
  have hxarg : (x : V → ℤ) ∈ argmaxB B (perturb ω (-p₀)) := by
    apply Finset.mem_filter.mpr
    refine ⟨x.property,?_⟩
    intro y hy
    simp only [perturb_neg]
    exact neg_le_neg (hmin ⟨y,hy⟩)
  have hxsuper : toReal (x : V → ℤ) ∈ superdiff (concaveConj B ω) p₀ := by
    intro q
    have hh := ciInf_le (Set.finite_range (fun y : (B : Set (V → ℤ)) => pairing q (toReal (y : V → ℤ))-ω y)).bddBelow x
    change concaveConj B ω q ≤ pairing q (toReal (x : V → ℤ))-ω x at hh
    rw [h0,pairing_sub_left]
    dsimp [a]
    linarith only [hh]
  have hlow (z : V → ℝ) (hz : z ∈ superdiff (concaveConj B ω) p₀) : b x ≤ pairing p z := by
    have hh := hz (p₀+t • p)
    rw [ht0,h0,pairing_sub_left,pairing_add_left,pairing_smul_left] at hh
    nlinarith only [hh,ht]
  have he : localization (concaveConj B ω) p₀ p=b x := by
    unfold localization
    have hbd : BddBelow ((fun z => pairing p z) '' superdiff (concaveConj B ω) p₀) := by
      refine ⟨b x,?_⟩
      rintro _ ⟨z,hz,rfl⟩
      exact hlow z hz
    apply le_antisymm (csInf_le hbd ⟨toReal (x : V → ℤ),hxsuper,rfl⟩)
    apply le_csInf (show ((fun z => pairing p z) '' superdiff (concaveConj B ω) p₀).Nonempty from ⟨_,⟨_,hxsuper,rfl⟩⟩)
    rintro _ ⟨z,hz,rfl⟩
    exact hlow z hz
  rw [he]
  constructor
  · exact ⟨x,hxarg,rfl⟩
  · rintro _ ⟨y,hy,rfl⟩
    have hy := Finset.mem_filter.mp hy
    apply hbmin ⟨y,hy.1⟩
    apply le_antisymm _ (hmin _)
    have hh := hy.2 x x.property
    simp only [perturb_neg] at hh
    exact neg_le_neg_iff.mp hh

end AttributedSteinitz.Localization

section
open SteinitzExchange.LocalSupermod
theorem checked_localization_eq_min_argmax {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) (p₀ p : V → ℝ) :
    IsLeast ((fun x => pairing p (toReal x)) '' (argmaxB B (perturb ω (-p₀)) : Set (V → ℤ)))
      (localization (concaveConj B ω) p₀ p) := by
  exact AttributedSteinitz.Localization.solution B hB ω p₀ p
end


namespace AttributedSteinitz.LocalCharacterization
-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.exc_iff_argmax_isIntegralBaseSet
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-01T19:33:14.292246+00:00
-- url     : https://prove2.me/submissions/99202e53-69d0-481b-8845-f8b5a45d264b


set_option autoImplicit false

-- Reuse the proved Theorem 4.4 from the Extension mission.
-- Its accepted reduction is by choi; dependencies include WillR,
-- mrfancypants, and the supporting-face/midpoint contributions of sometik179.
-- The two missions use definitionally identical exchange and maximizer predicates.
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : SteinitzExchange.LocalSupermod.IsIntegralBaseSet B)
    (ω : (V → ℤ) → ℝ) :
    SteinitzExchange.LocalSupermod.SatisfiesEXC B ω ↔
      ∀ p : V → ℝ, SteinitzExchange.LocalSupermod.IsIntegralBaseSet
        (SteinitzExchange.LocalSupermod.argmaxB B (SteinitzExchange.LocalSupermod.perturb ω p)) :=
  SteinitzExchange.Extension.exc_iff_argmax_isIntegralBaseSet B hB ω


end AttributedSteinitz.LocalCharacterization

section
open SteinitzExchange.LocalSupermod
theorem checked_exc_iff_argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : SteinitzExchange.LocalSupermod.IsIntegralBaseSet B)
    (ω : (V → ℤ) → ℝ) :
    SteinitzExchange.LocalSupermod.SatisfiesEXC B ω ↔
      ∀ p : V → ℝ, SteinitzExchange.LocalSupermod.IsIntegralBaseSet
        (SteinitzExchange.LocalSupermod.argmaxB B (SteinitzExchange.LocalSupermod.perturb ω p)) := by
  exact AttributedSteinitz.LocalCharacterization.solution B hB ω
end

section
open SteinitzExchange.LocalSupermod
theorem checked_base_saturated {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) :
    ∀ z : V → ℤ, toReal z ∈ hull B → z ∈ B := by
  intro z hz
  exact (AttributedSteinitz.Midpoint.SteinitzExchange.Extension.toReal_mem_hull_iff_checked
    B hB z).mp hz
end
end

/- Complete checked body: LocalizationBridge -/
section

open Set
open SteinitzExchange.LocalSupermod

namespace SteinitzExchange.LocalSupermodProof

theorem localization_eq_support {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (p₀ : V → ℝ) :
    localization (concaveConj B ω) p₀ = supportMin (argmaxB B (perturb ω (-p₀))) := by
  classical
  funext p
  let A := argmaxB B (perturb ω (-p₀))
  have h := checked_localization_eq_min_argmax B hB ω p₀ p
  obtain ⟨x, hx, he⟩ := h.1
  have : Finite (A : Set (V → ℤ)) := A.finite_toSet.to_subtype
  have : Nonempty (A : Set (V → ℤ)) := ⟨⟨x, hx⟩⟩
  apply le_antisymm
  · change localization (concaveConj B ω) p₀ p ≤
      ⨅ y : (A : Set (V → ℤ)), pairing p (toReal y.val)
    exact le_ciInf (fun y => h.2 ⟨y.val, y.property, rfl⟩)
  · have hh := ciInf_le (Set.finite_range
      (fun y : (A : Set (V → ℤ)) => pairing p (toReal y.val))).bddBelow ⟨x, hx⟩
    change supportMin A p ≤ pairing p (toReal x) at hh
    exact hh.trans_eq he

/-- The corrected Theorem 5.1 bridge includes its genuine integer-saturation premise. -/
theorem matroidal_iff_argmax_saturated {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (p₀ : V → ℝ)
    (hconv : ∀ z : V → ℤ, toReal z ∈ hull (argmaxB B (perturb ω (-p₀))) →
      z ∈ argmaxB B (perturb ω (-p₀))) :
    IsMatroidal (localization (concaveConj B ω) p₀) ↔
      IsIntegralBaseSet (argmaxB B (perturb ω (-p₀))) := by
  rw [localization_eq_support B hB ω p₀]
  exact (checked_baseSet_iff_support_matroidal _
    (argmax_nonempty B hB.1 (perturb ω (-p₀))) hconv).symm

end SteinitzExchange.LocalSupermodProof

end

/- Complete checked body: SteinitzRoot -/
section

open SteinitzExchange.LocalSupermodProof

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 292, Theorem 5.3 (Local Supermodularity Theorem), corrected. For `ω` on a
finite integral base set `B`: `ω` satisfies (EXC) iff `ω` coincides on `B` with its concave
closure `ω̂` (4.2) and the localization `L̂(ω°, p₀)` of the concave conjugate `ω°` (5.6) at
`p₀` ((5.8)–(5.9)) is "matroidal" at every `p₀ ∈ ℝ^V`. The printed statement omits the
concave-closure clause; without it the "if" direction fails
(see `localization_matroidal_not_sufficient`). -/
theorem exc_iff_localization_matroidal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ((∀ x ∈ B, concaveClosure B ω (toReal x) = ω x) ∧
        ∀ p₀ : V → ℝ, IsMatroidal (localization (concaveConj B ω) p₀)) := by
  constructor
  · intro hω
    refine ⟨checked_concaveClosure_eq_of_exc B hB ω hω, ?_⟩
    intro p₀
    have hA := (checked_exc_iff_argmax_isIntegralBaseSet B hB ω).mp hω (-p₀)
    exact (matroidal_iff_argmax_saturated B hB ω p₀
      (checked_base_saturated _ hA)).mpr hA
  · rintro ⟨hclosure, hlocal⟩
    apply (checked_exc_iff_argmax_isIntegralBaseSet B hB ω).mpr
    intro p
    have hconv := closure_agreement_argmax_saturated B hB.1
      (checked_base_saturated B hB) ω hclosure (-p)
    have h := (matroidal_iff_argmax_saturated B hB ω (-p) hconv).mp (hlocal (-p))
    simpa only [neg_neg] using h

end SteinitzExchange.LocalSupermod

end

open SteinitzExchange SteinitzExchange.LocalSupermod
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔
      ((∀ x ∈ B, concaveClosure B ω (toReal x) = ω x) ∧
        ∀ p₀ : V → ℝ, IsMatroidal (localization (concaveConj B ω) p₀)) := by
  exact SteinitzExchange.LocalSupermod.exc_iff_localization_matroidal B hB ω

#print axioms SteinitzExchange.LocalSupermod.exc_iff_localization_matroidal
#print axioms solution
