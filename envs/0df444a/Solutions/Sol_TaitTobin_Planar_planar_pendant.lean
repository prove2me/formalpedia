-- Prove2me | solution 1 for TaitTobin.Planar.planar_pendant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:34:08.074664+00:00
-- url     : https://prove2.me/submissions/aee19e3f-ac5d-4ee8-a678-8f91c6cfc616

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

set_option autoImplicit false

namespace TTPend

open RobertsonSeymour1986.GM5

/-- `S` is the image of an injective path from `P` to `Q`. -/
def ArcImg (P Q : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∃ γ : Path P Q, Function.Injective γ ∧ Set.range γ = S

lemma ArcImg.symm {P Q : ℝ × ℝ} {S : Set (ℝ × ℝ)} (h : ArcImg P Q S) : ArcImg Q P S := by
  obtain ⟨γ, hi, hr⟩ := h
  refine ⟨γ.symm, ?_, by rw [Path.symm_range, hr]⟩
  intro s t hst
  simp only [Path.symm_apply] at hst
  exact unitInterval.symm_involutive.injective (hi hst)

lemma ArcImg.trans {P Q R : ℝ × ℝ} {S T : Set (ℝ × ℝ)} (h1 : ArcImg P Q S)
    (h2 : ArcImg Q R T) (h : ∀ z, z ∈ S → z ∈ T → z = Q) : ArcImg P R (S ∪ T) := by
  obtain ⟨γ, hγ, rγ⟩ := h1
  obtain ⟨δ, hδ, rδ⟩ := h2
  refine ⟨γ.trans δ, ?_, by rw [Path.trans_range, rγ, rδ]⟩
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have e := congrArg Subtype.val (hγ hst)
    simp only at e
    exact Subtype.ext (by linarith)
  · exfalso
    have hz := h _ (rγ ▸ Set.mem_range_self _) (by rw [hst, ← rδ]; exact Set.mem_range_self _)
    have e1 := congrArg Subtype.val (hγ (hz.trans γ.target.symm))
    have e2 := congrArg Subtype.val (hδ ((hst.symm.trans hz).trans δ.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at e1 e2
    linarith
  · exfalso
    have hz := h _ (rγ ▸ Set.mem_range_self _) (by rw [← hst, ← rδ]; exact Set.mem_range_self _)
    have e1 := congrArg Subtype.val (hγ (hz.trans γ.target.symm))
    have e2 := congrArg Subtype.val (hδ ((hst.trans hz).trans δ.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at e1 e2
    linarith
  · have e := congrArg Subtype.val (hδ hst)
    simp only at e
    exact Subtype.ext (by linarith)

/-- the straight segment from `P` to `Q` -/
def seg (P Q : ℝ × ℝ) : Set (ℝ × ℝ) := (fun t : ℝ => P + t • (Q - P)) '' Set.Icc 0 1

def segPath (P Q : ℝ × ℝ) : Path P Q where
  toFun t := P + (t : ℝ) • (Q - P)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

lemma arcImg_seg {P Q : ℝ × ℝ} (h : P ≠ Q) : ArcImg P Q (seg P Q) := by
  refine ⟨segPath P Q, ?_, ?_⟩
  · intro s t hst
    have h' : (s : ℝ) • (Q - P) = (t : ℝ) • (Q - P) := by
      have e : P + (s : ℝ) • (Q - P) = P + (t : ℝ) • (Q - P) := hst
      exact add_left_cancel e
    have hne : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    exact Subtype.ext (smul_left_injective ℝ hne h')
  · ext z
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩

lemma seg_symm (P Q : ℝ × ℝ) : seg P Q = seg Q P := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    ext <;> simp <;> ring

lemma arcImg_sub {P Q : ℝ × ℝ} (γ : Path P Q) (hγ : Function.Injective γ) (a b : unitInterval)
    (hab : a < b) : ArcImg (γ a) (γ b) (γ '' Set.Icc a b) := by
  refine ⟨γ.subpath a b, ?_, Path.range_subpath_of_le γ a b hab.le⟩
  intro s t hst
  have e : γ (Set.Icc.convexComb a b s) = γ (Set.Icc.convexComb a b t) := hst
  have e2 := congrArg Subtype.val (hγ e)
  simp only [Set.Icc.coe_convexComb] at e2
  have hab' : (a : ℝ) < b := hab
  have : ((s : ℝ) - t) * ((b : ℝ) - a) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact Subtype.ext (by linarith)
  · exfalso; linarith

/-- Building a plane drawing from arc images. -/
theorem planar_of_imgs {V : Type} [LinearOrder V] (H : SimpleGraph V) (P : V → ℝ × ℝ)
    (hP : Function.Injective P) (S : V → V → Set (ℝ × ℝ))
    (hsymm : ∀ v w, S v w = S w v)
    (harc : ∀ v w, H.Adj v w → ArcImg (P v) (P w) (S v w))
    (havoid : ∀ v w, H.Adj v w → ∀ x, P x ∈ S v w → x = v ∨ x = w)
    (hmeet : ∀ v w x y, H.Adj v w → H.Adj x y → ¬ (s(v, w) = s(x, y)) →
      ∀ z, z ∈ S v w → z ∈ S x y → z = P v ∨ z = P w) :
    IsPlanar H := by
  classical
  let g : ∀ {v w : V}, H.Adj v w → Path (P v) (P w) := fun {v w} h =>
    if v < w then Classical.choose (harc v w h)
    else (Classical.choose (harc w v h.symm)).symm
  have gspec : ∀ {v w : V} (h : H.Adj v w),
      Function.Injective (g h) ∧ Set.range (g h) = S v w := by
    intro v w h
    by_cases hvw : v < w
    · simp only [g, if_pos hvw]; exact Classical.choose_spec (harc v w h)
    · simp only [g, if_neg hvw]
      obtain ⟨hi, hr⟩ := Classical.choose_spec (harc w v h.symm)
      refine ⟨?_, by rw [Path.symm_range, hr, hsymm]⟩
      intro s t hst
      simp only [Path.symm_apply] at hst
      exact unitInterval.symm_involutive.injective (hi hst)
  have grev : ∀ {v w : V} (h : H.Adj v w), g h.symm = (g h).symm := by
    intro v w h
    have hne : v ≠ w := H.ne_of_adj h
    rcases lt_or_gt_of_ne hne with hvw | hvw
    · simp only [g, if_pos hvw, if_neg (not_lt.mpr hvw.le)]
    · simp only [g, if_pos hvw, if_neg (not_lt.mpr hvw.le), Path.symm_symm]
  have hend : ∀ {v w : V} (h : H.Adj v w) (s : unitInterval),
      (g h s = P v ∨ g h s = P w) → (s = 0 ∨ s = 1) := by
    intro v w h s hs
    rcases hs with hs | hs
    · left; exact (gspec h).1 (hs.trans (g h).source.symm)
    · right; exact (gspec h).1 (hs.trans (g h).target.symm)
  refine ⟨PlaneDrawing.mk P hP g (fun h => (gspec h).1) (fun h => grev h) ?_ ?_⟩
  · intro v w h t x hx
    apply havoid v w h x
    rw [← (gspec h).2, ← hx]; exact Set.mem_range_self t
  · intro v w x y h k s t hst
    by_cases he : s(v, w) = s(x, y)
    · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, h2⟩
      · right; left; exact ⟨h1, h2⟩
    · right; right
      have hz1 : g h s ∈ S v w := (gspec h).2 ▸ Set.mem_range_self s
      have hz2 : g k t ∈ S x y := (gspec k).2 ▸ Set.mem_range_self t
      have he' : ¬ s(x, y) = s(v, w) := fun h' => he h'.symm
      refine ⟨hend h s (hmeet v w x y h k he _ hz1 (hst ▸ hz2)),
        hend k t (hmeet x y v w k h he' _ hz2 (hst ▸ hz1))⟩

/-- last exit time from a closed ball -/
lemma exit_time {A B : ℝ × ℝ} (γ : Path A B) {r : ℝ} (hr : 0 < r) (hB : r < dist B A) :
    ∃ τ : unitInterval, dist (γ τ) A = r ∧ ∀ t : unitInterval, τ < t → r < dist (γ t) A := by
  let S : Set unitInterval := {t | dist (γ t) A ≤ r}
  have hS : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have h0 : (0 : unitInterval) ∈ S := by
    show dist (γ 0) A ≤ r
    rw [γ.source, dist_self]; exact hr.le
  obtain ⟨τ, hτS, hmax⟩ := hS.isCompact.exists_isMaxOn ⟨0, h0⟩
    (continuous_subtype_val.continuousOn)
  have hgt : ∀ t : unitInterval, τ < t → r < dist (γ t) A := by
    intro t ht
    by_contra hle
    have hle' : t ∈ S := not_lt.mp hle
    have := isMaxOn_iff.mp hmax t hle'
    exact absurd ht (not_lt.mpr this)
  refine ⟨τ, ?_, hgt⟩
  apply le_antisymm hτS
  by_contra hlt
  have hlt' : dist (γ τ) A < r := not_le.mp hlt
  have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
  let f : ℝ → ℝ := fun s => dist (γ.extend s) A
  have hf : Continuous f := by fun_prop
  have hfτ : f τ = dist (γ τ) A := by
    show dist (γ.extend τ) A = _
    rw [Path.extend_extends']
  have hf1 : f 1 = dist B A := by
    show dist (γ.extend 1) A = _
    rw [Path.extend_one]
  have hrm : r ∈ Set.Icc (f τ) (f 1) := ⟨by rw [hfτ]; exact hlt'.le, by rw [hf1]; exact hB.le⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hτ1 hf.continuousOn hrm
  have hs01 : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans τ.2.1 hs.1, hs.2⟩
  have hsτ : (τ : ℝ) < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exfalso; rw [← h, hfτ] at hfs; linarith
    · exact h
  have h1 := hgt ⟨s, hs01⟩ hsτ
  have hfs' : f s = dist (γ ⟨s, hs01⟩) A := by
    show dist (γ.extend s) A = _
    rw [Path.extend_apply γ hs01]
  linarith


lemma fin_min {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c > 0, ∀ i, c ≤ f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  | inr _ =>
    obtain ⟨i0, hi0⟩ := Finite.exists_min f
    exact ⟨f i0, hf i0, hi0⟩

lemma pos_min_path {P Q : ℝ × ℝ} (γ : Path P Q) (A : ℝ × ℝ) (h : ∀ t, γ t ≠ A) :
    ∃ c > 0, ∀ t, c ≤ dist (γ t) A := by
  obtain ⟨t0, -, ht0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (Continuous.continuousOn (by fun_prop : Continuous fun t => dist (γ t) A))
  exact ⟨dist (γ t0) A, dist_pos.mpr (h t0), fun t => isMinOn_iff.mp ht0 t (Set.mem_univ t)⟩

lemma dist_smul_add (A v : ℝ × ℝ) {t : ℝ} (ht : 0 ≤ t) : dist (A + t • v) A = t * ‖v‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]

lemma seg_dist_le {A p z : ℝ × ℝ} (hz : z ∈ seg A p) : dist z A ≤ dist p A := by
  obtain ⟨t, ht, rfl⟩ := hz
  rw [dist_smul_add A _ ht.1, dist_eq_norm p A]
  calc t * ‖p - A‖ ≤ 1 * ‖p - A‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ = ‖p - A‖ := one_mul _

lemma seg_dist_eq {A p z : ℝ × ℝ} (hp : p ≠ A) (hz : z ∈ seg A p) (h : dist z A = dist p A) :
    z = p := by
  obtain ⟨t, ht, rfl⟩ := hz
  rw [dist_smul_add A _ ht.1, dist_eq_norm p A] at h
  have hn : 0 < ‖p - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  have ht1 : t = 1 := by
    have h2 : (t - 1) * ‖p - A‖ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · linarith
    · linarith
  subst ht1; simp

lemma seg_seg {A p q z : ℝ × ℝ} (hpq : p ≠ q) (hd : dist p A = dist q A) (hz1 : z ∈ seg A p)
    (hz2 : z ∈ seg A q) : z = A := by
  obtain ⟨s, hs, rfl⟩ := hz1
  obtain ⟨t, ht, e⟩ := hz2
  have hd1 := congrArg (fun z => dist z A) e
  simp only at hd1
  rw [dist_smul_add A _ ht.1, dist_smul_add A _ hs.1, ← dist_eq_norm, ← dist_eq_norm, hd] at hd1
  by_cases hq : dist q A = 0
  · exfalso; apply hpq
    rw [hq, dist_eq_zero] at hd
    rw [dist_eq_zero] at hq
    rw [hd, hq]
  · have hts : t = s := mul_right_cancel₀ hq hd1
    subst hts
    by_cases ht0 : t = 0
    · subst ht0; simp
    · exfalso; apply hpq
      have e2 : t • (q - A) = t • (p - A) := add_left_cancel e
      have e3 : q - A = p - A := smul_right_injective (ℝ × ℝ) ht0 e2
      exact (sub_left_injective e3).symm

lemma seg_free {A p z : ℝ × ℝ} {r σ : ℝ} (hr : 0 < r) (_hp : p ≠ A)
    (hσ : ¬ (0 < (p - A).1 ∧ (p - A).2 = σ * (p - A).1))
    (hz1 : z ∈ seg A (A + (r / 2) • ((1 : ℝ), σ))) (hz2 : z ∈ seg A p) : z = A := by
  obtain ⟨s, hs, rfl⟩ := hz1
  obtain ⟨t, ht, e⟩ := hz2
  have e2 : t • (p - A) = s • ((r / 2) • ((1 : ℝ), σ)) := by
    have e' := add_left_cancel e
    rw [e', add_sub_cancel_left]
  have c1 := congrArg Prod.fst e2
  have c2 := congrArg Prod.snd e2
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul,
    mul_one] at c1 c2
  by_cases hs0 : s = 0
  · subst hs0; simp
  · exfalso
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : s * (r / 2) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hs0 h
      · linarith
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    apply hσ
    have hpos : 0 < t * (p.1 - A.1) := by rw [c1]; positivity
    refine ⟨pos_of_mul_pos_right hpos htpos.le, ?_⟩
    have : t * (p.2 - A.2) = t * (σ * (p.1 - A.1)) := by rw [c2]; linear_combination (-σ) * c1
    exact mul_left_cancel₀ ht0 this

theorem pendant_main {n : ℕ} (G : SimpleGraph (Fin n)) (D : PlaneDrawing G)
    (u a : Fin n) (hua : u ≠ a) (hu : ∀ q, ¬ G.Adj u q)
    (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔ (G.Adj p q ∨ (p = u ∧ q = a) ∨ (q = u ∧ p = a))) :
    IsPlanar G' := by
  classical
  have hvert : ∀ v : Fin n, ∃ c > 0, v ≠ a → c ≤ dist (D.vertex v) (D.vertex a) := by
    intro v
    by_cases hv : v = a
    · exact ⟨1, one_pos, fun h => absurd hv h⟩
    · exact ⟨_, dist_pos.mpr (fun e => hv (D.vertex_injective e)), fun _ => le_rfl⟩
  have hedge : ∀ p : Fin n × Fin n, ∃ c > 0, ∀ h : G.Adj p.1 p.2, p.1 ≠ a → p.2 ≠ a →
      ∀ t, c ≤ dist (D.arc h t) (D.vertex a) := by
    intro p
    by_cases hp : G.Adj p.1 p.2 ∧ p.1 ≠ a ∧ p.2 ≠ a
    · obtain ⟨c, hc, hle⟩ := pos_min_path (D.arc hp.1) (D.vertex a) (by
        intro t ht
        rcases D.arc_avoids_vertices hp.1 t a ht with h | h
        · exact hp.2.1 h.symm
        · exact hp.2.2 h.symm)
      exact ⟨c, hc, fun h _ _ t => hle t⟩
    · exact ⟨1, one_pos, fun h h1 h2 => absurd ⟨h, h1, h2⟩ hp⟩
  choose cv hcv0 hcv using hvert
  choose ce hce0 hce using hedge
  obtain ⟨c1, hc1, hc1le⟩ := fin_min cv hcv0
  obtain ⟨c2, hc2, hc2le⟩ := fin_min ce hce0
  obtain ⟨A, hAdef⟩ : ∃ A, A = D.vertex a := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = min c1 c2 / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; exact half_pos (lt_min hc1 hc2)
  have hrv : ∀ v, v ≠ a → r < dist (D.vertex v) A := by
    intro v hv
    have h1 := hcv v hv
    have h2 := hc1le v
    have h3 : min c1 c2 ≤ c1 := min_le_left _ _
    have h4 : 0 < min c1 c2 := lt_min hc1 hc2
    rw [hAdef]; rw [hrdef]; linarith
  have hre : ∀ v w (h : G.Adj v w), v ≠ a → w ≠ a → ∀ t, r < dist (D.arc h t) A := by
    intro v w h hv hw t
    have h1 := hce (v, w) h hv hw t
    have h2 := hc2le (v, w)
    have h3 : min c1 c2 ≤ c2 := min_le_right _ _
    have h4 : 0 < min c1 c2 := lt_min hc1 hc2
    rw [hAdef]; rw [hrdef]; linarith
  have hex : ∀ b : Fin n, ∃ τ : unitInterval, ∀ h : G.Adj a b,
      dist (D.arc h τ) A = r ∧ ∀ t : unitInterval, τ < t → r < dist (D.arc h t) A := by
    intro b
    by_cases h : G.Adj a b
    · have hb : r < dist (D.vertex b) (D.vertex a) := by
        rw [← hAdef]; exact hrv b (G.ne_of_adj h).symm
      obtain ⟨τ, h1, h2⟩ := exit_time (D.arc h) hr hb
      exact ⟨τ, fun _ => ⟨by rw [hAdef]; exact h1, by rw [hAdef]; exact h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose τ hτ using hex
  have hbu : ∀ b, G.Adj a b → b ≠ u := fun b h e => hu a (e ▸ h).symm
  have hvu : ∀ v w, G.Adj v w → v ≠ u := fun v w h e => hu w (e ▸ h)
  have hτ1 : ∀ b (h : G.Adj a b), τ b < 1 := by
    intro b h
    refine lt_of_le_of_ne (unitInterval.le_one _) (fun e => ?_)
    have h1 := (hτ b h).1
    rw [e, (D.arc h).target] at h1
    have := hrv b (G.ne_of_adj h).symm
    linarith
  have hτ0 : ∀ b (h : G.Adj a b), τ b ≠ 0 := by
    intro b h e
    have h1 := (hτ b h).1
    rw [e, (D.arc h).source, ← hAdef, dist_self] at h1
    linarith
  obtain ⟨p, hp⟩ : ∃ p : Fin n → ℝ × ℝ, ∀ b (h : G.Adj a b), p b = D.arc h (τ b) :=
    ⟨fun b => if h : G.Adj a b then D.arc h (τ b) else A, fun b h => dif_pos h⟩
  have hpd : ∀ b, G.Adj a b → dist (p b) A = r := fun b h => by rw [hp b h]; exact (hτ b h).1
  have hpA : ∀ b, G.Adj a b → p b ≠ A := fun b h e => by
    have := hpd b h; rw [e, dist_self] at this; linarith
  obtain ⟨Out, hOut⟩ : ∃ Out : Fin n → Set (ℝ × ℝ), ∀ b (h : G.Adj a b),
      Out b = (D.arc h) '' Set.Icc (τ b) 1 :=
    ⟨fun b => if h : G.Adj a b then (D.arc h) '' Set.Icc (τ b) 1 else ∅, fun b h => dif_pos h⟩
  have hOut_ge : ∀ b, G.Adj a b → ∀ z ∈ Out b, r ≤ dist z A ∧ (dist z A = r → z = p b) := by
    intro b h z hz
    rw [hOut b h] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rcases eq_or_lt_of_le ht.1 with e | e
    · rw [← e, ← hp b h]; exact ⟨(hpd b h).ge, fun _ => rfl⟩
    · have := (hτ b h).2 t e; exact ⟨this.le, fun h' => absurd h' (ne_of_gt this)⟩
  obtain ⟨Str, hStr⟩ : ∃ Str : Fin n → Set (ℝ × ℝ), ∀ b, Str b = seg A (p b) ∪ Out b :=
    ⟨_, fun b => rfl⟩
  have hStr_arc : ∀ b, G.Adj a b → ArcImg A (D.vertex b) (Str b) := by
    intro b h
    have h1 : ArcImg A (p b) (seg A (p b)) := arcImg_seg (hpA b h).symm
    have h2 : ArcImg (p b) (D.vertex b) (Out b) := by
      have := arcImg_sub (D.arc h) (D.arc_injective h) (τ b) 1 (hτ1 b h)
      rw [(D.arc h).target, ← hp b h, ← hOut b h] at this; exact this
    rw [hStr b]
    refine h1.trans h2 ?_
    intro z hz1 hz2
    obtain ⟨hge, heq⟩ := hOut_ge b h z hz2
    have hle := seg_dist_le hz1; rw [hpd b h] at hle
    exact heq (le_antisymm hle hge)
  -- the free direction
  obtain ⟨σ, hσI, hσB⟩ : ∃ σ ∈ Set.Icc (-1 : ℝ) 1,
      σ ∉ (Finset.univ.image (fun b : Fin n => (p b - A).2 / (p b - A).1)) :=
    (Set.Icc_infinite (by norm_num : (-1:ℝ) < 1)).exists_notMem_finset _
  have hσ : ∀ b, ¬ (0 < (p b - A).1 ∧ (p b - A).2 = σ * (p b - A).1) := by
    rintro b ⟨h1, h2⟩
    apply hσB
    rw [Finset.mem_image]
    exact ⟨b, Finset.mem_univ _, (div_eq_iff (ne_of_gt h1)).mpr h2⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ × ℝ, Q = A + (r / 2) • ((1 : ℝ), σ) := ⟨_, rfl⟩
  have hQd : dist Q A = r / 2 := by
    rw [hQdef, dist_smul_add A _ (by positivity), Prod.norm_def]
    have h1 : ‖(1 : ℝ)‖ = 1 := norm_one
    have h2 : ‖σ‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; exact ⟨hσI.1, hσI.2⟩
    simp only
    rw [h1, max_eq_left h2, mul_one]
  have hQA : Q ≠ A := fun e => by rw [e, dist_self] at hQd; linarith
  have hQseg : ∀ z ∈ seg A Q, dist z A ≤ r / 2 := fun z hz => (seg_dist_le hz).trans hQd.le
  -- meeting facts
  have M12 : ∀ b, G.Adj a b → ∀ z, z ∈ seg A Q → z ∈ Str b → z = A := by
    intro b h z hz1 hz2
    rw [hStr b] at hz2
    rcases hz2 with hz2 | hz2
    · exact seg_free hr (hpA b h) (hσ b) (hQdef ▸ hz1) hz2
    · exfalso
      have := (hOut_ge b h z hz2).1
      have := hQseg z hz1
      linarith
  have M13 : ∀ v w (h : G.Adj v w), v ≠ a → w ≠ a → ∀ z, z ∈ seg A Q →
      z ∈ Set.range (D.arc h) → False := by
    intro v w h hv hw z hz1 hz2
    obtain ⟨t, rfl⟩ := hz2
    have := hre v w h hv hw t
    have := hQseg _ hz1
    linarith
  have hpp : ∀ b c, G.Adj a b → G.Adj a c → b ≠ c → p b ≠ p c := by
    intro b c hb hc hbc e
    rw [hp b hb, hp c hc] at e
    rcases D.arcs_meet_only_at_endpoints hb hc (τ b) (τ c) e with ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact hbc h2
    · exact G.ne_of_adj hb h2.symm
    · rcases h1 with h1 | h1
      · exact hτ0 b hb h1
      · exact absurd h1 (ne_of_lt (hτ1 b hb))
  have hOut_arc : ∀ b (h : G.Adj a b), ∀ z ∈ Out b, ∃ s : unitInterval, τ b ≤ s ∧ s ≠ 0 ∧
      D.arc h s = z := by
    intro b h z hz
    rw [hOut b h] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    refine ⟨s, hs.1, fun e => hτ0 b h ?_, rfl⟩
    exact le_antisymm (e ▸ hs.1) unitInterval.nonneg'
  have M22 : ∀ b c, G.Adj a b → G.Adj a c → b ≠ c → ∀ z, z ∈ Str b → z ∈ Str c → z = A := by
    intro b c hb hc hbc z hz1 hz2
    rw [hStr b] at hz1
    rw [hStr c] at hz2
    rcases hz1 with hz1 | hz1 <;> rcases hz2 with hz2 | hz2
    · exact seg_seg (hpp b c hb hc hbc) ((hpd b hb).trans (hpd c hc).symm) hz1 hz2
    · exfalso
      obtain ⟨hge, heq⟩ := hOut_ge c hc z hz2
      have hle := seg_dist_le hz1; rw [hpd b hb] at hle
      have e1 := heq (le_antisymm hle hge)
      have e2 := seg_dist_eq (hpA b hb) hz1 (by rw [hpd b hb]; exact le_antisymm hle hge)
      exact hpp b c hb hc hbc (e2.symm.trans e1)
    · exfalso
      obtain ⟨hge, heq⟩ := hOut_ge b hb z hz1
      have hle := seg_dist_le hz2; rw [hpd c hc] at hle
      have e1 := heq (le_antisymm hle hge)
      have e2 := seg_dist_eq (hpA c hc) hz2 (by rw [hpd c hc]; exact le_antisymm hle hge)
      exact hpp b c hb hc hbc (e1.symm.trans e2)
    · exfalso
      obtain ⟨s, -, hs0, rfl⟩ := hOut_arc b hb z hz1
      obtain ⟨t, -, ht0, e⟩ := hOut_arc c hc _ hz2
      rcases D.arcs_meet_only_at_endpoints hb hc s t e.symm with ⟨_, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩
      · exact hbc h2
      · exact G.ne_of_adj hb h2.symm
      · rcases h1 with h1 | h1
        · exact hs0 h1
        · rcases h2 with h2 | h2
          · exact ht0 h2
          · rw [h1, (D.arc hb).target] at e
            rw [h2, (D.arc hc).target] at e
            exact hbc (D.vertex_injective e).symm
  have M23 : ∀ b, G.Adj a b → ∀ v w (h : G.Adj v w), v ≠ a → w ≠ a → ∀ z, z ∈ Str b →
      z ∈ Set.range (D.arc h) → z = D.vertex b ∧ (z = D.vertex v ∨ z = D.vertex w) := by
    intro b hb v w h hv hw z hz1 hz2
    rw [hStr b] at hz1
    obtain ⟨t, rfl⟩ := hz2
    rcases hz1 with hz1 | hz1
    · exfalso
      have := seg_dist_le hz1; rw [hpd b hb] at this
      have := hre v w h hv hw t
      linarith
    · obtain ⟨s, -, hs0, e⟩ := hOut_arc b hb _ hz1
      rcases D.arcs_meet_only_at_endpoints hb h s t e with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact absurd h1.symm hv
      · exact absurd h1.symm hw
      · rcases h1 with h1 | h1
        · exact absurd h1 hs0
        · refine ⟨by rw [← e, h1, (D.arc hb).target], ?_⟩
          rcases h2 with h2 | h2
          · left; rw [h2, (D.arc h).source]
          · right; rw [h2, (D.arc h).target]
  have M33 : ∀ v w x y (h : G.Adj v w) (k : G.Adj x y), ¬ s(v, w) = s(x, y) → ∀ z,
      z ∈ Set.range (D.arc h) → z ∈ Set.range (D.arc k) → z = D.vertex v ∨ z = D.vertex w := by
    intro v w x y h k hne z hz1 hz2
    obtain ⟨s, rfl⟩ := hz1
    obtain ⟨t, e⟩ := hz2
    rcases D.arcs_meet_only_at_endpoints h k s t e.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact absurd (by rw [h1, h2]) hne
    · exact absurd (by rw [h1, h2, Sym2.eq_swap]) hne
    · rcases h1 with h1 | h1
      · left; rw [h1, (D.arc h).source]
      · right; rw [h1, (D.arc h).target]
  -- the new drawing
  let P' : Fin n → ℝ × ℝ := Function.update D.vertex u Q
  have hP'u : P' u = Q := Function.update_self u Q D.vertex
  have hP'v : ∀ v, v ≠ u → P' v = D.vertex v := fun v hv => Function.update_of_ne hv Q D.vertex
  have hP'a : P' a = A := by rw [hP'v a hua.symm, hAdef]
  have hP'inj : Function.Injective P' := by
    intro v w e
    by_cases hv : v = u <;> by_cases hw : w = u
    · rw [hv, hw]
    · exfalso
      rw [hv, hP'u, hP'v w hw] at e
      by_cases hwa : w = a
      · rw [hwa, ← hAdef] at e; exact hQA e
      · have := hrv w hwa; rw [← e, hQd] at this; linarith
    · exfalso
      rw [hw, hP'u, hP'v v hv] at e
      by_cases hva : v = a
      · rw [hva, ← hAdef] at e; exact hQA e.symm
      · have := hrv v hva; rw [e, hQd] at this; linarith
    · rw [hP'v v hv, hP'v w hw] at e; exact D.vertex_injective e
  let S' : Fin n → Fin n → Set (ℝ × ℝ) := fun v w =>
    if (v = u ∧ w = a) ∨ (v = a ∧ w = u) then seg A Q
    else if v = a then Str w
    else if w = a then Str v
    else if h : G.Adj v w then Set.range (D.arc h) else ∅
  have hSua : S' u a = seg A Q := if_pos (Or.inl ⟨rfl, rfl⟩)
  have hSau : S' a u = seg A Q := if_pos (Or.inr ⟨rfl, rfl⟩)
  have hSab : ∀ b, G.Adj a b → S' a b = Str b := by
    intro b h
    have hb := hbu b h
    have c1 : ¬ ((a = u ∧ b = a) ∨ (a = a ∧ b = u)) := by
      rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact hua h1.symm
      · exact hb h2
    simp only [S', if_neg c1, ↓reduceIte]
  have hSba : ∀ b, G.Adj a b → S' b a = Str b := by
    intro b h
    have hb := hbu b h
    have hba : b ≠ a := (G.ne_of_adj h).symm
    have c1 : ¬ ((b = u ∧ a = a) ∨ (b = a ∧ a = u)) := by
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hb h1
      · exact hba h1
    simp only [S', if_neg c1, if_neg hba, ↓reduceIte]
  have hSvw : ∀ v w (h : G.Adj v w), v ≠ a → w ≠ a → S' v w = Set.range (D.arc h) := by
    intro v w h hv hw
    have c1 : ¬ ((v = u ∧ w = a) ∨ (v = a ∧ w = u)) := by
      rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · exact hw h2
      · exact hv h1
    simp only [S', if_neg c1, if_neg hv, if_neg hw, dif_pos h]
  have hcls : ∀ v w, G'.Adj v w → (v = u ∧ w = a) ∨ (v = a ∧ w = u) ∨ (G.Adj v w ∧ v = a) ∨
      (G.Adj v w ∧ w = a) ∨ (G.Adj v w ∧ v ≠ a ∧ w ≠ a) := by
    intro v w h
    rcases (hG' v w).mp h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hv : v = a
      · exact Or.inr (Or.inr (Or.inl ⟨h, hv⟩))
      · by_cases hw : w = a
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hw⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hv, hw⟩)))
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  have hsymm : ∀ v w, S' v w = S' w v := by
    intro v w
    by_cases h1 : (v = u ∧ w = a) ∨ (v = a ∧ w = u)
    · have h1' : (w = u ∧ v = a) ∨ (w = a ∧ v = u) := by tauto
      simp only [S', if_pos h1, if_pos h1']
    · have h1' : ¬ ((w = u ∧ v = a) ∨ (w = a ∧ v = u)) := by tauto
      simp only [S', if_neg h1, if_neg h1']
      by_cases hv : v = a
      · by_cases hw : w = a
        · rw [hv, hw]
        · simp only [if_pos hv, if_neg hw]
      · by_cases hw : w = a
        · simp only [if_pos hw, if_neg hv]
        · simp only [if_neg hv, if_neg hw]
          by_cases hvw : G.Adj v w
          · rw [dif_pos hvw, dif_pos hvw.symm, D.arc_reverse hvw, Path.symm_range]
          · rw [dif_neg hvw, dif_neg (fun h => hvw h.symm)]
  refine planar_of_imgs G' P' hP'inj S' hsymm ?_ ?_ ?_
  · -- arcs
    intro v w h
    rcases hcls v w h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, hv, hw⟩
    · rw [hSua, hP'u, hP'a]; exact (arcImg_seg (Ne.symm hQA)).symm
    · rw [hSau, hP'u, hP'a]; exact arcImg_seg (Ne.symm hQA)
    · rw [hSab w hg, hP'a, hP'v w (hbu w hg)]; exact hStr_arc w hg
    · rw [hSba v hg.symm, hP'a, hP'v v (hbu v hg.symm)]; exact (hStr_arc v hg.symm).symm
    · rw [hSvw v w hg hv hw, hP'v v (hvu v w hg), hP'v w (hvu w v hg.symm)]
      exact ⟨D.arc hg, D.arc_injective hg, rfl⟩
  · -- vertices
    intro v w h x hx
    rcases hcls v w h with ⟨hv1, hw1⟩ | ⟨hv1, hw1⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, hv, hw⟩
    · rw [hv1, hw1] at hx ⊢
      rw [hSua] at hx
      by_cases hxu : x = u
      · left; exact hxu
      · right
        by_contra hxa
        rw [hP'v x hxu] at hx
        have := hQseg _ hx; have := hrv x hxa; linarith
    · rw [hv1, hw1] at hx ⊢
      rw [hSau] at hx
      by_cases hxu : x = u
      · right; exact hxu
      · left
        by_contra hxa
        rw [hP'v x hxu] at hx
        have := hQseg _ hx; have := hrv x hxa; linarith
    · rw [hSab w hg] at hx
      by_cases hxu : x = u
      · exfalso
        rw [hxu, hP'u] at hx
        have hQ : Q ∈ seg A Q := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
        have := M12 w hg Q hQ hx
        exact hQA this
      · rw [hP'v x hxu, hStr w] at hx
        rcases hx with hx | hx
        · left
          by_contra hxa
          have := seg_dist_le hx; rw [hpd w hg] at this
          have := hrv x hxa; linarith
        · obtain ⟨s, -, -, e⟩ := hOut_arc w hg _ hx
          rcases D.arc_avoids_vertices hg s x e with h1 | h1
          · left; exact h1
          · right; exact h1
    · rw [hSba v hg.symm] at hx
      by_cases hxu : x = u
      · exfalso
        rw [hxu, hP'u] at hx
        have hQ : Q ∈ seg A Q := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp⟩
        have := M12 v hg.symm Q hQ hx
        exact hQA this
      · rw [hP'v x hxu, hStr v] at hx
        rcases hx with hx | hx
        · right
          by_contra hxa
          have := seg_dist_le hx; rw [hpd v hg.symm] at this
          have := hrv x hxa; linarith
        · obtain ⟨s, -, -, e⟩ := hOut_arc v hg.symm _ hx
          rcases D.arc_avoids_vertices hg.symm s x e with h1 | h1
          · right; exact h1
          · left; exact h1
    · rw [hSvw v w hg hv hw] at hx
      obtain ⟨t, ht⟩ := hx
      by_cases hxu : x = u
      · exfalso
        rw [hxu, hP'u] at ht
        have := hre v w hg hv hw t
        rw [ht, hQd] at this; linarith
      · rw [hP'v x hxu] at ht
        exact D.arc_avoids_vertices hg t x ht
  · -- meeting
    intro v w x y h k hne z hz1 hz2
    have hQs : ∀ z, z ∈ seg A Q → z ∈ seg A Q := fun z h => h
    rcases hcls v w h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, hv, hw⟩ <;>
    rcases hcls x y k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨kg, rfl⟩ | ⟨kg, rfl⟩ | ⟨kg, hx, hy⟩
    -- first edge (u,a)
    · exact absurd rfl hne
    · exact absurd Sym2.eq_swap hne
    · rw [hSua] at hz1; rw [hSab y kg] at hz2
      right; rw [hP'a]; exact M12 y kg z hz1 hz2
    · rw [hSua] at hz1; rw [hSba x kg.symm] at hz2
      right; rw [hP'a]; exact M12 x kg.symm z hz1 hz2
    · rw [hSua] at hz1; rw [hSvw x y kg hx hy] at hz2
      exact (M13 x y kg hx hy z hz1 hz2).elim
    -- first edge (a,u)
    · exact absurd Sym2.eq_swap hne
    · exact absurd rfl hne
    · rw [hSau] at hz1; rw [hSab y kg] at hz2
      left; rw [hP'a]; exact M12 y kg z hz1 hz2
    · rw [hSau] at hz1; rw [hSba x kg.symm] at hz2
      left; rw [hP'a]; exact M12 x kg.symm z hz1 hz2
    · rw [hSau] at hz1; rw [hSvw x y kg hx hy] at hz2
      exact (M13 x y kg hx hy z hz1 hz2).elim
    -- first edge (a,w)
    · rw [hSab w hg] at hz1; rw [hSua] at hz2
      left; rw [hP'a]; exact M12 w hg z hz2 hz1
    · rw [hSab w hg] at hz1; rw [hSau] at hz2
      left; rw [hP'a]; exact M12 w hg z hz2 hz1
    · rw [hSab w hg] at hz1; rw [hSab y kg] at hz2
      left; rw [hP'a]
      exact M22 w y hg kg (fun e => hne (by rw [e])) z hz1 hz2
    · rw [hSab w hg] at hz1; rw [hSba x kg.symm] at hz2
      left; rw [hP'a]
      exact M22 w x hg kg.symm (fun e => hne (by rw [e, Sym2.eq_swap])) z hz1 hz2
    · rw [hSab w hg] at hz1; rw [hSvw x y kg hx hy] at hz2
      right; rw [hP'v w (hbu w hg)]; exact (M23 w hg x y kg hx hy z hz1 hz2).1
    -- first edge (v,a)
    · rw [hSba v hg.symm] at hz1; rw [hSua] at hz2
      right; rw [hP'a]; exact M12 v hg.symm z hz2 hz1
    · rw [hSba v hg.symm] at hz1; rw [hSau] at hz2
      right; rw [hP'a]; exact M12 v hg.symm z hz2 hz1
    · rw [hSba v hg.symm] at hz1; rw [hSab y kg] at hz2
      right; rw [hP'a]
      exact M22 v y hg.symm kg (fun e => hne (by rw [e, Sym2.eq_swap])) z hz1 hz2
    · rw [hSba v hg.symm] at hz1; rw [hSba x kg.symm] at hz2
      right; rw [hP'a]
      exact M22 v x hg.symm kg.symm (fun e => hne (by rw [e])) z hz1 hz2
    · rw [hSba v hg.symm] at hz1; rw [hSvw x y kg hx hy] at hz2
      left; rw [hP'v v (hbu v hg.symm)]; exact (M23 v hg.symm x y kg hx hy z hz1 hz2).1
    -- first edge (v,w) old
    · rw [hSvw v w hg hv hw] at hz1; rw [hSua] at hz2
      exact (M13 v w hg hv hw z hz2 hz1).elim
    · rw [hSvw v w hg hv hw] at hz1; rw [hSau] at hz2
      exact (M13 v w hg hv hw z hz2 hz1).elim
    · rw [hSvw v w hg hv hw] at hz1; rw [hSab y kg] at hz2
      rw [hP'v v (hvu v w hg), hP'v w (hvu w v hg.symm)]
      exact (M23 y kg v w hg hv hw z hz2 hz1).2
    · rw [hSvw v w hg hv hw] at hz1; rw [hSba x kg.symm] at hz2
      rw [hP'v v (hvu v w hg), hP'v w (hvu w v hg.symm)]
      exact (M23 x kg.symm v w hg hv hw z hz2 hz1).2
    · rw [hSvw v w hg hv hw] at hz1; rw [hSvw x y kg hx hy] at hz2
      rw [hP'v v (hvu v w hg), hP'v w (hvu w v hg.symm)]
      exact M33 v w x y hg kg hne z hz1 hz2

end TTPend

open RobertsonSeymour1986.GM5 in
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (u a : Fin n) (hua : u ≠ a) (hu : ∀ q, ¬ G.Adj u q)
    (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔
      (G.Adj p q ∨ (p = u ∧ q = a) ∨ (q = u ∧ p = a))) :
    IsPlanar G' := by
  obtain ⟨D⟩ := hG
  exact TTPend.pendant_main G D u a hua hu G' hG'
