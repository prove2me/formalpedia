-- Prove2me | solution 1 for SteinitzExchange.Extension.argmaxOn_perturbed_eq_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:16:36.929486+00:00
-- url     : https://prove2.me/submissions/b13c3c12-5c2f-4be5-9299-1f417fe13176

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

/-!
# Murota library for a7631793 (SteinitzExchange.Extension.exc_iff_concave_extension)

Stage S1: easy parts of the Extension Theorem + difference-constraint potentials.
Stage S2: Lemma 4.5 (EXC gives a supergradient at every point of `B`).
Stage S3: Thm 2.1 (simultaneous exchange) and (2.3) (`hull B ∩ ℤ^V = B`).
All declarations take explicit binders (no `variable` blocks).
-/

set_option autoImplicit false

namespace SteinitzExchange.Extension

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

/-! ## S1.2 Deliverable (a): the concave closure is concave on `B̄` -/

theorem murota_concaveClosure_concaveOn {V : Type*} [Fintype V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    ConcaveOn ℝ (hull B) (concaveClosure B g) := by
  refine ⟨by unfold hull; exact convex_convexHull ℝ _, ?_⟩
  intro x hx y hy a t ha ht hat
  show a • concaveClosure B g x + t • concaveClosure B g y ≤ concaveClosure B g (a • x + t • y)
  conv_rhs => unfold concaveClosure
  refine le_ciInf fun p => ?_
  have h1 := murota_concaveClosure_le B hB g hx p
  have h2 := murota_concaveClosure_le B hB g hy p
  rw [murota_pairing_add_right, murota_pairing_smul_right, murota_pairing_smul_right,
    smul_eq_mul, smul_eq_mul]
  have e2 : a * concaveConj B g p + t * concaveConj B g p = concaveConj B g p := by
    rw [← add_mul, hat, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 ht]

/-- Child 3365fe25, exact form. -/
theorem concaveClosure_concaveOn {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    ConcaveOn ℝ (hull B) (concaveClosure B g) :=
  murota_concaveClosure_concaveOn B hB g

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

theorem murota_argmaxB_perturb_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (ω : (V → ℤ) → ℝ) (hω : SatisfiesEXC B ω)
    (p : V → ℝ) : IsIntegralBaseSet (argmaxB B (perturb ω p)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x0, hx0, hmax⟩ := B.exists_max_image (perturb ω p) hB
    exact ⟨x0, by rw [argmaxB, Finset.mem_filter]; exact ⟨hx0, hmax⟩⟩
  · intro x hx y hy u hu
    rw [argmaxB, Finset.mem_filter] at hx hy
    obtain ⟨v, hv, hx', hy', hle⟩ := hω x hx.1 y hy.1 u hu
    refine ⟨v, hv, ?_⟩
    rw [argmaxB, Finset.mem_filter]
    refine ⟨hx', fun z hz => ?_⟩
    have key := murota_perturb_exchange_sum ω p x y u v
    have h1 := hy.2 (y + chi u - chi v) hy'
    have h2 := hx.2 z hz
    unfold perturb at key h1 h2 ⊢
    linarith

/-! ## S1.5 Deliverable (d): `argmax(ĝ[p]) = conv(argmax(g[p]))` -/

theorem murota_argmaxOn_concaveClosure_eq_hull {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    argmaxOn (hull B) (concaveClosure B g) = hull (argmaxB B g) := by
  obtain ⟨x0, hx0, hmax⟩ := B.exists_max_image g hB
  have hA : ∀ x, x ∈ argmaxB B g ↔ x ∈ B ∧ g x = g x0 := by
    intro x
    rw [argmaxB, Finset.mem_filter]
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, le_antisymm (hmax x hx) (h x0 hx0)⟩
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun y hy => h ▸ hmax y hy⟩
  have hsub : hull (argmaxB B g) ⊆ hull B := by
    unfold hull
    apply convexHull_mono
    apply Set.image_mono
    intro x hx
    exact Finset.mem_coe.mpr ((hA x).1 (Finset.mem_coe.mp hx)).1
  have hle : ∀ b ∈ hull B, concaveClosure B g b ≤ g x0 :=
    fun b hb => murota_concaveClosure_le_of_le B hB g (g x0) hmax hb
  have hge : ∀ b ∈ hull (argmaxB B g), g x0 ≤ concaveClosure B g b := by
    have hconv := (murota_concaveClosure_concaveOn B hB g).convex_ge (g x0)
    intro b hb
    have hs : toReal '' ((argmaxB B g : Finset (V → ℤ)) : Set (V → ℤ)) ⊆
        {b | b ∈ hull B ∧ g x0 ≤ concaveClosure B g b} := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' := (hA x).1 (Finset.mem_coe.mp hx)
      refine ⟨subset_convexHull ℝ _ ⟨x, Finset.mem_coe.mpr hx'.1, rfl⟩, ?_⟩
      rw [← hx'.2]
      exact murota_le_concaveClosure B g hx'.1
    exact (convexHull_min hs hconv hb).2
  ext b
  constructor
  · rintro ⟨hb, hbmax⟩
    by_contra hnot
    have hx0mem : toReal x0 ∈ hull B := subset_convexHull ℝ _ ⟨x0, Finset.mem_coe.mpr hx0, rfl⟩
    have hMb : g x0 ≤ concaveClosure B g b :=
      (murota_le_concaveClosure B g hx0).trans (hbmax _ hx0mem)
    have hfin : (toReal '' ((argmaxB B g : Finset (V → ℤ)) : Set (V → ℤ))).Finite :=
      (argmaxB B g).finite_toSet.image _
    have hclosed : IsClosed (hull (argmaxB B g)) := (hfin.isCompact_convexHull ℝ).isClosed
    have hconvA : Convex ℝ (hull (argmaxB B g)) := by unfold hull; exact convex_convexHull ℝ _
    obtain ⟨f, u, hfb, hfA⟩ := geometric_hahn_banach_point_closed hconvA hclosed hnot
    set q : V → ℝ := fun v => f (fun j => if v = j then 1 else 0) with hq
    have hfq : ∀ c, f c = pairing q c := by
      intro c
      have := LinearMap.pi_apply_eq_sum_univ f.toLinearMap c
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this, pairing]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hq, mul_comm]
    -- for each x ∈ B, eventually (t → 0+) the perturbed value is below the max
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ x ∈ B,
        t * (pairing q b - pairing q (toReal x)) + g x < g x0 := by
      rw [Filter.eventually_all_finset]
      intro x hx
      by_cases hgx : g x = g x0
      · have hxA : x ∈ argmaxB B g := (hA x).2 ⟨hx, hgx⟩
        have hxhull : toReal x ∈ hull (argmaxB B g) :=
          subset_convexHull ℝ _ ⟨x, Finset.mem_coe.mpr hxA, rfl⟩
        have h1 := hfA _ hxhull
        rw [hfq] at h1 hfb
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (0 : ℝ) < t := ht
        have hneg : pairing q b - pairing q (toReal x) < 0 := by linarith
        have := mul_neg_of_pos_of_neg ht' hneg
        linarith
      · have hlt : g x < g x0 := lt_of_le_of_ne (hmax x hx) hgx
        have htend : Filter.Tendsto (fun t : ℝ => t * (pairing q b - pairing q (toReal x)) + g x)
            (nhds 0) (nhds (0 * (pairing q b - pairing q (toReal x)) + g x)) := by
          exact ((continuous_id.mul continuous_const).add continuous_const).tendsto 0
        rw [zero_mul, zero_add] at htend
        exact nhdsWithin_le_nhds (htend.eventually (gt_mem_nhds hlt))
    obtain ⟨t, ht, _⟩ := (hev.and self_mem_nhdsWithin).exists
    have hcl := murota_concaveClosure_le B hB g hb (t • q)
    obtain ⟨x1, hx1, hx1e⟩ := murota_exists_concaveConj_eq B hB g (t • q)
    rw [hx1e, murota_pairing_smul_left, murota_pairing_smul_left] at hcl
    have := ht x1 hx1
    have e : t * pairing q b - (t * pairing q (toReal x1) - g x1) =
        t * (pairing q b - pairing q (toReal x1)) + g x1 := by ring
    linarith
  · intro hb
    exact ⟨hsub hb, fun c hc => (hle c hc).trans (hge b hb)⟩

theorem murota_concaveConj_perturb {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (g : (V → ℤ) → ℝ) (p q : V → ℝ) :
    concaveConj B (perturb g p) q = concaveConj B g (q - p) := by
  unfold concaveConj perturb
  congr 1
  funext x
  rw [murota_pairing_sub_left]
  ring

theorem murota_concaveClosure_perturb {V : Type*} [Fintype V] (B : Finset (V → ℤ))
    (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) {b : V → ℝ} (hb : b ∈ hull B) :
    concaveClosure B (perturb g p) b = concaveClosure B g b + pairing p b := by
  unfold concaveClosure
  simp_rw [murota_concaveConj_perturb]
  have e : ∀ q : V → ℝ, pairing q b - concaveConj B g (q - p) =
      (fun r : V → ℝ => pairing r b - concaveConj B g r + pairing p b) ((Equiv.subRight p) q) := by
    intro q
    simp only [Equiv.subRight_apply]
    rw [murota_pairing_sub_left]
    ring
  rw [iInf_congr e, Equiv.iInf_comp (g := fun r : V → ℝ => pairing r b - concaveConj B g r + pairing p b)]
  exact (ciInf_add (murota_bddBelow_family B hB g hb) (pairing p b)).symm

/-- Child 17853cd0, exact form. -/
theorem murota_argmaxOn_perturbed_eq_hull {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) :
    argmaxOn (hull B) (fun b => concaveClosure B g b + pairing p b) = hull (argmaxB B (perturb g p)) := by
  have h : argmaxOn (hull B) (fun b => concaveClosure B g b + pairing p b) =
      argmaxOn (hull B) (concaveClosure B (perturb g p)) := by
    ext b
    simp only [argmaxOn, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hb, h⟩
      refine ⟨hb, fun c hc => ?_⟩
      rw [murota_concaveClosure_perturb B hB g p hc, murota_concaveClosure_perturb B hB g p hb]
      exact h c hc
    · rintro ⟨hb, h⟩
      refine ⟨hb, fun c hc => ?_⟩
      have := h c hc
      rw [murota_concaveClosure_perturb B hB g p hc, murota_concaveClosure_perturb B hB g p hb] at this
      exact this
  rw [h, murota_argmaxOn_concaveClosure_eq_hull B hB (perturb g p)]

end SteinitzExchange.Extension

open SteinitzExchange.Extension in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p : V → ℝ) :
    argmaxOn (hull B) (fun b => concaveClosure B g b + pairing p b) = hull (argmaxB B (perturb g p)) := by
  exact murota_argmaxOn_perturbed_eq_hull B hB g p

#print axioms solution
