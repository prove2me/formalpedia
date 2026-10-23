-- Prove2me | solution 1 for SimplicialIso.Cheeger.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:38:34.301894+00:00
-- url     : https://prove2.me/submissions/b9af35aa-9557-4f92-8e55-2dff60472df4

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting

set_option autoImplicit false

namespace SimplicialIso.Cheeger.Aux17

open SimplicialIso.Cheeger Finset

variable {n d : ℕ}

lemma app_eq_ev {k : ℕ} (f : Form n k) (σ : Cell n k) : f σ = ev f σ.1 := by
  unfold ev; rw [dif_pos σ.2]

lemma ev_of_ne {k : ℕ} (f : Form n k) (s : Finset (Fin n)) (h : s.card ≠ k) : ev f s = 0 := by
  unfold ev; rw [dif_neg h]

lemma sum_cell {k : ℕ} (F : Finset (Fin n) → ℝ) :
    ∑ σ : Cell n k, F σ.1 = ∑ s : Finset (Fin n), if s.card = k then F s else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter (fun s : Finset (Fin n) => s.card = k))
    (by simp) F).symm

lemma inner_eq_sum {k : ℕ} (f g : Form n k) :
    inner ℝ f g = ∑ s : Finset (Fin n), ev f s * ev g s := by
  rw [PiLp.inner_apply]
  have : ∀ σ : Cell n k, inner ℝ (f σ) (g σ) = ev f σ.1 * ev g σ.1 := by
    intro σ; rw [app_eq_ev, app_eq_ev, Real.inner_apply]
  simp_rw [this]
  rw [sum_cell (fun s => ev f s * ev g s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rfl
  · rw [ev_of_ne f s h, zero_mul]

lemma sgn_insert (s : Finset (Fin n)) (v w : Fin n) (hv : v ∉ s) :
    sgn (insert v s) w = (if v < w then -1 else 1) * sgn s w := by
  unfold sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hv]), pow_succ]; ring
  · ring

lemma sgn_insert_self (s : Finset (Fin n)) (v : Fin n) (hv : v ∉ s) :
    sgn (insert v s) v = sgn s v := by
  rw [sgn_insert s v v hv]; simp

lemma sgn_mul_self (s : Finset (Fin n)) (v : Fin n) : sgn s v * sgn s v = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

lemma ev_cobd (X : Complex n d) (f : Form n d) (t : Finset (Fin n)) :
    ev (cobdTop X f) t = if t ∈ X.top then ∑ v ∈ t, sgn t v * ev f (t.erase v) else 0 := by
  by_cases h1 : t.card = d + 1
  · rw [show ev (cobdTop X f) t = (cobdTop X f) ⟨t, h1⟩ from dif_pos h1]
    rfl
  · rw [ev_of_ne _ t h1, if_neg (fun h2 => h1 (X.card_top t h2))]

lemma ev_bd (X : Complex n d) (g : Form n (d + 1)) (s : Finset (Fin n)) (hs : s.card = d) :
    ev (bdTop X g) s = ∑ v ∈ univ.filter (fun v => v ∉ s ∧ insert v s ∈ X.top),
      sgn (insert v s) v * ev g (insert v s) := by
  unfold ev; rw [dif_pos hs]; rfl

/-- adjointness of `bdTop` and `cobdTop` -/
lemma inner_bd (X : Complex n d) (g : Form n (d + 1)) (h : Form n d) :
    inner ℝ (bdTop X g) h = inner ℝ g (cobdTop X h) := by
  rw [inner_eq_sum, inner_eq_sum]
  have L : ∀ s : Finset (Fin n), ev (bdTop X g) s * ev h s =
      ∑ v : Fin n, if v ∉ s ∧ insert v s ∈ X.top then
        sgn (insert v s) v * ev g (insert v s) * ev h ((insert v s).erase v) else 0 := by
    intro s
    by_cases hs : s.card = d
    · rw [ev_bd X g s hs, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs with hc
      · rw [Finset.erase_insert hc.1]
      · simp
    · rw [ev_of_ne h s hs, mul_zero]
      symm; refine Finset.sum_eq_zero fun v _ => ?_
      split_ifs with hc
      · exfalso; apply hs
        have := X.card_top _ hc.2
        rw [Finset.card_insert_of_notMem hc.1] at this; omega
      · rfl
  have R : ∀ t : Finset (Fin n), ev g t * ev (cobdTop X h) t =
      ∑ v : Fin n, if v ∈ t ∧ t ∈ X.top then
        sgn t v * ev g t * ev h (t.erase v) else 0 := by
    intro t
    rw [ev_cobd]
    split_ifs with ht
    · rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      have : univ.filter (fun v => v ∈ t ∧ t ∈ X.top) = t := by
        ext v; simp [ht]
      rw [this]
      refine Finset.sum_congr rfl fun v _ => by ring
    · rw [mul_zero]; symm; refine Finset.sum_eq_zero fun v _ => ?_
      rw [if_neg (by tauto)]
  simp_rw [L, R]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun t v => if v ∈ t ∧ t ∈ X.top then
        sgn t v * ev g t * ev h (t.erase v) else 0)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun s => insert v s) (fun t => t.erase v)
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨Finset.mem_insert_self _ _, hs.2⟩
  · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [Finset.insert_erase ht.1]; exact ⟨Finset.notMem_erase _ _, ht.2⟩
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.erase_insert hs.1
  · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact Finset.insert_erase ht.1
  · intro s _; rfl

/-- `∂_{d-1} ∂_d = 0` -/
lemma bdLow_bdTop (hd : 1 ≤ d) (X : Complex n d) (g : Form n (d + 1)) :
    bdLow n d (bdTop X g) = 0 := by
  ext ρ
  have hρ := ρ.2
  show (∑ v ∈ univ.filter (fun v => v ∉ ρ.1),
    sgn (insert v ρ.1) v * ev (bdTop X g) (insert v ρ.1)) = 0
  set r := ρ.1 with hr
  let H : Fin n → Fin n → ℝ := fun v w =>
    if v ∉ r ∧ w ∉ insert v r ∧ insert w (insert v r) ∈ X.top then
      sgn (insert v r) v * (sgn (insert w (insert v r)) w * ev g (insert w (insert v r))) else 0
  have hsum : (∑ v ∈ univ.filter (fun v => v ∉ r),
      sgn (insert v r) v * ev (bdTop X g) (insert v r)) = ∑ v : Fin n, ∑ w : Fin n, H v w := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ r
    · rw [if_neg (not_not.mpr hv)]
      symm; refine Finset.sum_eq_zero fun w _ => ?_
      simp only [H]; rw [if_neg (by tauto)]
    · rw [if_pos hv]
      have hc : (insert v r).card = d := by
        rw [Finset.card_insert_of_notMem hv, hρ]; omega
      rw [ev_bd X g _ hc, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [H]
      split_ifs with h1 h2 h2
      · rfl
      · exact (h2 ⟨hv, h1⟩).elim
      · exact (h1 ⟨h2.2.1, h2.2.2⟩).elim
      · simp
  have hanti : ∀ v w, H w v = - H v w := by
    intro v w
    simp only [H]
    by_cases hc : v ∉ r ∧ w ∉ insert v r ∧ insert w (insert v r) ∈ X.top
    · have hvw : v ≠ w := by
        intro e; apply hc.2.1; rw [e]; exact Finset.mem_insert_self _ _
      have hw : w ∉ r := fun h => hc.2.1 (Finset.mem_insert_of_mem h)
      have hc' : w ∉ r ∧ v ∉ insert w r ∧ insert v (insert w r) ∈ X.top := by
        refine ⟨hw, ?_, ?_⟩
        · simp [hc.1, hvw]
        · rw [Finset.insert_comm]; exact hc.2.2
      rw [if_pos hc, if_pos hc', Finset.insert_comm w v r]
      rw [sgn_insert_self _ _ hc.1, sgn_insert_self _ _ hw,
        sgn_insert_self (insert w r) v hc'.2.1, sgn_insert r w v hw,
        sgn_insert (insert w r) v w hc'.2.1, sgn_insert_self r w hw]
      rcases lt_or_gt_of_ne hvw with h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
    · have hc' : ¬ (w ∉ r ∧ v ∉ insert w r ∧ insert v (insert w r) ∈ X.top) := by
        rintro ⟨h1, h2, h3⟩
        apply hc
        have hvw : v ≠ w := by
          intro e; apply h2; rw [e]; exact Finset.mem_insert_self _ _
        refine ⟨fun h => h2 (Finset.mem_insert_of_mem h), ?_, ?_⟩
        · simp [h1, hvw.symm]
        · rw [Finset.insert_comm]; exact h3
      rw [if_neg hc, if_neg hc', neg_zero]
  rw [hsum]
  have hS : ∑ v : Fin n, ∑ w : Fin n, H v w = - ∑ v : Fin n, ∑ w : Fin n, H v w := by
    calc ∑ v : Fin n, ∑ w : Fin n, H v w = ∑ v : Fin n, ∑ w : Fin n, H w v := Finset.sum_comm
      _ = ∑ v : Fin n, ∑ w : Fin n, - H v w :=
          Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => hanti v w
      _ = - ∑ v : Fin n, ∑ w : Fin n, H v w := by simp only [Finset.sum_neg_distrib]
  show _ = (0 : Form n (d - 1)) ρ
  simp only [PiLp.zero_apply]
  linarith

/-! ## Orientation signs relative to a partition -/

section Part

variable (p : Fin n → Fin (d + 1))

def tt (x y : Fin n) : ℝ := if x < y ∧ p y < p x then -1 else 1

def eps (s : Finset (Fin n)) : ℝ := ∏ x ∈ s, ∏ y ∈ s, tt p x y

def pre (s : Finset (Fin n)) (v : Fin n) : ℝ := ∏ z ∈ s, if p z < p v then (-1 : ℝ) else 1

lemma sgn_eq_prod (s : Finset (Fin n)) (v : Fin n) :
    sgn s v = ∏ z ∈ s, if z < v then (-1 : ℝ) else 1 := by
  unfold sgn; rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma eps_insert (s : Finset (Fin n)) (v : Fin n) (hv : v ∉ s) :
    eps p (insert v s) = (∏ y ∈ s, tt p v y) * (∏ x ∈ s, tt p x v) * eps p s := by
  unfold eps
  simp only [Finset.prod_insert hv, Finset.prod_mul_distrib]
  rw [show tt p v v = 1 by simp [tt]]
  ring

lemma sgn_eps_insert (s : Finset (Fin n)) (v : Fin n) (hv : v ∉ s)
    (hp : ∀ z ∈ s, p z ≠ p v) :
    sgn (insert v s) v * eps p (insert v s) = pre p s v * eps p s := by
  rw [sgn_insert_self s v hv, eps_insert p s v hv, sgn_eq_prod]
  unfold pre
  rw [show ∀ a b c e : ℝ, a * (b * c * e) = (a * b * c) * e by intros; ring,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun z hz => ?_
  have hzv : z ≠ v := fun e => hv (e ▸ hz)
  have hpz := hp z hz
  unfold tt
  rcases lt_or_gt_of_ne hzv with h | h <;> rcases lt_or_gt_of_ne hpz with h' | h' <;>
    simp [h, h', not_lt.mpr h.le, not_lt.mpr h'.le]

lemma eps_mul_self (s : Finset (Fin n)) : eps p s * eps p s = 1 := by
  unfold eps
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun y _ => ?_
  unfold tt; split_ifs <;> norm_num

/-- rainbow sets: one vertex in each block -/
def R (t : Finset (Fin n)) : Prop := t.card = d + 1 ∧ t.image p = univ

instance : DecidablePred (R p) := fun t => by unfold R; infer_instance

lemma R_inj {t : Finset (Fin n)} (ht : R p t) : Set.InjOn p t := by
  apply Finset.card_image_iff.mp
  rw [ht.2, Finset.card_univ, Fintype.card_fin, ht.1]

lemma R_card {t : Finset (Fin n)} (ht : R p t) : t.card = d + 1 := ht.1

lemma R_insert_ne {s : Finset (Fin n)} {w : Fin n} (hR : R p (insert w s)) (hw : w ∉ s) :
    ∀ z ∈ s, p z ≠ p w := by
  intro z hz e
  have := R_inj p hR (Finset.mem_insert_of_mem hz) (Finset.mem_insert_self _ _) e
  exact hw (this ▸ hz)

lemma R_swap {t : Finset (Fin n)} (ht : R p t) {v w : Fin n} (hv : v ∈ t)
    (hw : w ∉ t.erase v) : R p (insert w (t.erase v)) ↔ p w = p v := by
  by_cases hwv : w = v
  · subst hwv; rw [Finset.insert_erase hv]; exact iff_of_true ht rfl
  have hwt : w ∉ t := fun h => hw (Finset.mem_erase.mpr ⟨hwv, h⟩)
  have hcard : (insert w (t.erase v)).card = d + 1 := by
    rw [Finset.card_insert_of_notMem hw, Finset.card_erase_of_mem hv, ht.1]; omega
  constructor
  · intro h
    have hpv : p v ∈ (insert w (t.erase v)).image p := by rw [h.2]; exact Finset.mem_univ _
    rw [Finset.image_insert, Finset.mem_insert] at hpv
    rcases hpv with e | hpv
    · exact e.symm
    · obtain ⟨z, hz, e⟩ := Finset.mem_image.mp hpv
      have hz' := Finset.mem_erase.mp hz
      exact absurd (R_inj p ht hz'.2 hv e) hz'.1
  · intro e
    refine ⟨hcard, ?_⟩
    rw [Finset.image_insert, e, ← Finset.image_insert, Finset.insert_erase hv, ht.2]

lemma notR_pair {t : Finset (Fin n)} (hc : t.card = d + 1) (hn : ¬ R p t) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ p x = p y := by
  by_contra h
  apply hn
  refine ⟨hc, Finset.eq_univ_of_card _ ?_⟩
  rw [Finset.card_image_of_injOn (fun x hx y hy e => by
    by_contra hxy; exact h ⟨x, hx, y, hy, hxy, e⟩), hc, Fintype.card_fin]

def cnt (s : Finset (Fin n)) : ℝ :=
  ∑ w ∈ univ.filter (fun w => w ∉ s ∧ R p (insert w s)), pre p s w

def gT : Form n (d + 1) := WithLp.toLp 2 (fun τ => if R p τ.1 then eps p τ.1 else 0)

def fT : Form n d := WithLp.toLp 2 (fun σ => cnt p σ.1 * eps p σ.1)

lemma ev_gT (t : Finset (Fin n)) : ev (gT p) t = if R p t then eps p t else 0 := by
  by_cases h : t.card = d + 1
  · rw [show ev (gT p) t = (gT p) ⟨t, h⟩ from dif_pos h]; rfl
  · rw [ev_of_ne _ t h, if_neg (fun hR => h hR.1)]

lemma ev_fT (s : Finset (Fin n)) (hs : s.card = d) : ev (fT p) s = cnt p s * eps p s := by
  rw [show ev (fT p) s = (fT p) ⟨s, hs⟩ from dif_pos hs]; rfl

/-- the complete `d`-complex -/
def full : Complex n d := ⟨univ.filter (fun t => t.card = d + 1), by simp⟩

lemma fT_eq : fT p = bdTop full (gT p) := by
  ext σ
  rw [app_eq_ev (bdTop full (gT p)), ev_bd _ _ _ σ.2]
  show cnt p σ.1 * eps p σ.1 = _
  unfold cnt
  rw [Finset.sum_mul, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ev_gT]
  by_cases hw : w ∉ σ.1
  · by_cases hR : R p (insert w σ.1)
    · have hfull : insert w σ.1 ∈ (full : Complex n d).top := by
        simp [full, R_card p hR]
      rw [if_pos ⟨hw, hR⟩, if_pos ⟨hw, hfull⟩, if_pos hR,
        sgn_eps_insert p _ _ hw (R_insert_ne p hR hw)]
    · rw [if_neg (fun h => hR h.2), if_neg hR]; split_ifs <;> simp
  · rw [if_neg (fun h => hw h.1), if_neg (fun h => hw h.1)]

lemma fT_cycle (hd : 1 ≤ d) : fT p ∈ cycles n d := by
  unfold cycles; rw [LinearMap.mem_ker, fT_eq]; exact bdLow_bdTop hd _ _

lemma swap_sign {s : Finset (Fin n)} {x y : Fin n} (hxy : x ≠ y) (hx : x ∉ s) (hy : y ∉ s)
    (hpxy : p x = p y) (hp : ∀ z ∈ s, p z ≠ p x) :
    sgn (insert x (insert y s)) x * eps p (insert y s) =
      - (sgn (insert x (insert y s)) y * eps p (insert x s)) := by
  have Ly := sgn_eps_insert p s y hy (fun z hz => by rw [← hpxy]; exact hp z hz)
  have Lx := sgn_eps_insert p s x hx hp
  rw [sgn_insert_self _ _ hy] at Ly
  rw [sgn_insert_self _ _ hx] at Lx
  have ey : eps p (insert y s) = sgn s y * pre p s y * eps p s := by
    calc eps p (insert y s) = (sgn s y * sgn s y) * eps p (insert y s) := by
          rw [sgn_mul_self, one_mul]
      _ = sgn s y * (sgn s y * eps p (insert y s)) := by ring
      _ = _ := by rw [Ly]; ring
  have ex : eps p (insert x s) = sgn s x * pre p s y * eps p s := by
    have : pre p s x = pre p s y := by unfold pre; rw [hpxy]
    calc eps p (insert x s) = (sgn s x * sgn s x) * eps p (insert x s) := by
          rw [sgn_mul_self, one_mul]
      _ = sgn s x * (sgn s x * eps p (insert x s)) := by ring
      _ = _ := by rw [Lx, this]; ring
  have hx' : x ∉ insert y s := by simp [hx, hxy]
  rw [sgn_insert_self _ _ hx', sgn_insert s y x hy, sgn_insert (insert y s) x y hx',
    sgn_insert_self _ _ hy, ey, ex]
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring

lemma cobd_fT_val {t : Finset (Fin n)} (hc : t.card = d + 1) :
    ∑ v ∈ t, sgn t v * ev (fT p) (t.erase v) = if R p t then (n : ℝ) * eps p t else 0 := by
  have hev : ∀ v ∈ t, ev (fT p) (t.erase v) = cnt p (t.erase v) * eps p (t.erase v) := by
    intro v hv; apply ev_fT; rw [Finset.card_erase_of_mem hv, hc]; rfl
  rw [Finset.sum_congr rfl fun v hv => by rw [hev v hv]]
  split_ifs with hR
  · have hterm : ∀ v ∈ t, sgn t v * (cnt p (t.erase v) * eps p (t.erase v)) =
        ((univ.filter (fun w => p w = p v)).card : ℝ) * eps p t := by
      intro v hv
      have hcnt : cnt p (t.erase v) =
          ((univ.filter (fun w => p w = p v)).card : ℝ) * pre p (t.erase v) v := by
        unfold cnt
        have hfil : univ.filter (fun w => w ∉ t.erase v ∧ R p (insert w (t.erase v))) =
            univ.filter (fun w => p w = p v) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩; exact (R_swap p hR hv h1).mp h2
          · intro e
            have h1 : w ∉ t.erase v := by
              intro hw
              have hw' := Finset.mem_erase.mp hw
              exact hw'.1 (R_inj p hR hw'.2 hv e)
            exact ⟨h1, (R_swap p hR hv h1).mpr e⟩
        rw [hfil, Finset.sum_congr rfl (g := fun _ => pre p (t.erase v) v), Finset.sum_const,
          nsmul_eq_mul]
        intro w hw
        have e : p w = p v := (Finset.mem_filter.mp hw).2
        unfold pre; rw [e]
      have L := sgn_eps_insert p (t.erase v) v (Finset.notMem_erase v t) (fun z hz e =>
        (Finset.mem_erase.mp hz).1 (R_inj p hR (Finset.mem_erase.mp hz).2 hv e))
      rw [Finset.insert_erase hv] at L
      rw [hcnt, show ∀ a b c e : ℝ, a * (b * c * e) = b * (a * (c * e)) by intros; ring, ← L,
        ← mul_assoc (sgn t v), sgn_mul_self, one_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    have himg : ∑ v ∈ t, ((univ.filter (fun w => p w = p v)).card : ℝ) =
        ∑ i ∈ t.image p, ((univ.filter (fun w => p w = i)).card : ℝ) := by
      rw [Finset.sum_image (fun x hx y hy e => R_inj p hR hx hy e)]
    rw [himg, hR.2]
    have := Finset.card_eq_sum_card_fiberwise (f := p) (s := (univ : Finset (Fin n)))
      (t := (univ : Finset (Fin (d + 1)))) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  · obtain ⟨x, hx, y, hy, hxy, hpxy⟩ := notR_pair p hc hR
    set s := (t.erase x).erase y with hs
    have hyx : y ∈ t.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
    have htx : t.erase x = insert y s := (Finset.insert_erase hyx).symm
    have hxy' : x ∈ t.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
    have hty : t.erase y = insert x s := by
      rw [hs, Finset.erase_right_comm, Finset.insert_erase hxy']
    have ht : t = insert x (insert y s) := by rw [← htx, Finset.insert_erase hx]
    have hxs : x ∉ s := by simp [hs]
    have hys : y ∉ s := by simp [hs]
    have hzero : ∀ v ∈ t, v ≠ x ∧ v ≠ y →
        sgn t v * (cnt p (t.erase v) * eps p (t.erase v)) = 0 := by
      rintro v hv ⟨hvx, hvy⟩
      have : cnt p (t.erase v) = 0 := by
        unfold cnt
        refine Finset.sum_eq_zero fun w hw => ?_
        exfalso
        have hw' := (Finset.mem_filter.mp hw).2
        have hxm : x ∈ insert w (t.erase v) :=
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvx.symm, hx⟩)
        have hym : y ∈ insert w (t.erase v) :=
          Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvy.symm, hy⟩)
        exact hxy (R_inj p hw'.2 hxm hym hpxy)
      rw [this]; ring
    rw [Finset.sum_eq_add_of_mem x y hx hy hxy hzero]
    have hcnt : cnt p (t.erase x) = cnt p (t.erase y) := by
      unfold cnt
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      have hpre : pre p (t.erase x) w = pre p (t.erase y) w := by
        rw [htx, hty]; unfold pre; rw [Finset.prod_insert hys, Finset.prod_insert hxs, hpxy]
      rw [hpre]
      refine if_congr ?_ rfl rfl
      by_cases hwx : w = x
      · subst hwx
        rw [Finset.insert_erase hx]
        exact iff_of_false (fun h => hR h.2) (fun h => h.1 hxy')
      by_cases hwy : w = y
      · subst hwy
        rw [Finset.insert_erase hy]
        exact iff_of_false (fun h => h.1 hyx) (fun h => hR h.2)
      have hmx : w ∉ t.erase x ↔ w ∉ t := by simp [hwx]
      have hmy : w ∉ t.erase y ↔ w ∉ t := by simp [hwy]
      rw [hmx, hmy]
      refine and_congr_right fun hwt => ?_
      rw [htx, hty]
      have hws : w ∉ s := fun h => hwt (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      have hc1 : (insert w (insert y s)).card = (insert w (insert x s)).card := by
        rw [Finset.card_insert_of_notMem (by simp [hwy, hws]), Finset.card_insert_of_notMem hys,
          Finset.card_insert_of_notMem (by simp [hwx, hws]), Finset.card_insert_of_notMem hxs]
      have hi : (insert w (insert y s)).image p = (insert w (insert x s)).image p := by
        simp only [Finset.image_insert, hpxy]
      unfold R; rw [hc1, hi]
    rw [hcnt]
    by_cases hps : ∀ z ∈ s, p z ≠ p x
    · have hsw := swap_sign p hxy hxs hys hpxy hps
      rw [← ht, ← htx, ← hty] at hsw
      linear_combination (cnt p (t.erase y)) * hsw
    · obtain ⟨z, hz, hpz⟩ : ∃ z ∈ s, p z = p x := by
        by_contra h; exact hps fun z hz e => h ⟨z, hz, e⟩
      have : cnt p (t.erase y) = 0 := by
        unfold cnt
        refine Finset.sum_eq_zero fun w hw => ?_
        exfalso
        have hw' := (Finset.mem_filter.mp hw).2
        rw [hty] at hw'
        have := R_inj p hw'.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
          (Finset.mem_insert_of_mem (Finset.mem_insert_self x s)) hpz
        exact hxs (this ▸ hz)
      rw [this]; ring

lemma ev_cobd_fT (Y : Complex n d) (t : Finset (Fin n)) :
    ev (cobdTop Y (fT p)) t = if t ∈ Y.top ∧ R p t then (n : ℝ) * eps p t else 0 := by
  rw [ev_cobd]
  by_cases ht : t ∈ Y.top
  · rw [if_pos ht, cobd_fT_val p (Y.card_top t ht)]; simp [ht]
  · rw [if_neg ht]; simp [ht]

lemma norm_fT : inner ℝ (fT p) (fT p) = (n : ℝ) * ((univ.filter (R p)).card : ℝ) := by
  have h := inner_bd full (gT p) (fT p)
  rw [← fT_eq] at h
  rw [h, inner_eq_sum, ← Finset.sum_boole, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ev_gT, ev_cobd_fT]
  by_cases hR : R p t
  · have hf : t ∈ (full : Complex n d).top := by simp [full, R_card p hR]
    rw [if_pos hR, if_pos ⟨hf, hR⟩, if_pos hR,
      show ∀ a b : ℝ, a * (b * a) = b * (a * a) by intros; ring, eps_mul_self, mul_one]
  · simp [hR]

lemma lap_fT (X : Complex n d) :
    inner ℝ (upLap X (fT p)) (fT p) = (n : ℝ) ^ 2 * ((X.top.filter (R p)).card : ℝ) := by
  have h : inner ℝ (upLap X (fT p)) (fT p) = inner ℝ (cobdTop X (fT p)) (cobdTop X (fT p)) := by
    unfold upLap; exact inner_bd X _ _
  have hf : X.top.filter (R p) = univ.filter (fun t => t ∈ X.top ∧ R p t) := by
    ext t; simp
  rw [h, inner_eq_sum, hf, ← Finset.sum_boole, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ev_cobd_fT]
  split_ifs with h1
  · rw [show ∀ a b : ℝ, a * b * (a * b) = a ^ 2 * (b * b) by intros; ring, eps_mul_self]
  · simp

lemma card_R_ge : (∏ i, ((univ.filter (fun w => p w = i)).card : ℝ)) ≤
    ((univ.filter (R p)).card : ℝ) := by
  rw [← Nat.cast_prod]
  apply Nat.cast_le.mpr
  rw [← Fintype.card_piFinset]
  apply Finset.card_le_card_of_injOn (fun φ => univ.image φ)
  · intro φ hφ
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hφ
    have hφ' : ∀ i, p (φ i) = i := fun i => (Finset.mem_filter.mp (hφ i)).2
    have hinj : Function.Injective φ := fun i j e => by rw [← hφ' i, ← hφ' j, e]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin], ?_⟩
    rw [Finset.image_image]
    apply Finset.eq_univ_of_forall
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hφ' i⟩
  · intro φ hφ ψ hψ e
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hφ hψ
    have hφ' : ∀ i, p (φ i) = i := fun i => (Finset.mem_filter.mp (hφ i)).2
    have hψ' : ∀ i, p (ψ i) = i := fun i => (Finset.mem_filter.mp (hψ i)).2
    have e' : univ.image φ = univ.image ψ := e
    funext i
    have hm : φ i ∈ univ.image ψ := e' ▸ Finset.mem_image_of_mem φ (Finset.mem_univ i)
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := by rw [← hψ' j, hj, hφ' i]
    subst hji
    exact hj.symm

lemma pos_fT (hn : 1 ≤ n) (hsurj : ∀ i, ∃ v, p v = i) : 0 < inner ℝ (fT p) (fT p) := by
  rw [norm_fT]
  have hge := card_R_ge p
  have hprod : 0 < ∏ i, ((univ.filter (fun w => p w = i)).card : ℝ) := by
    refine Finset.prod_pos fun i _ => ?_
    obtain ⟨v, hv⟩ := hsurj i
    exact_mod_cast Finset.card_pos.mpr ⟨v, by simp [hv]⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hn' (lt_of_lt_of_le hprod hge)

lemma fT_ne (hn : 1 ≤ n) (hsurj : ∀ i, ∃ v, p v = i) : fT p ≠ 0 := by
  intro h
  have := pos_fT p hn hsurj
  rw [h, inner_zero_left] at this
  exact lt_irrefl _ this

end Part

lemma part_fun (A : Fin (d + 1) → Finset (Fin n)) (hA : IsPartition A) :
    ∃ p : Fin n → Fin (d + 1), ∀ v i, v ∈ A i ↔ p v = i := by
  choose p hp using hA.2.2
  refine ⟨p, fun v i => ⟨fun hv => ?_, fun e => e ▸ hp v⟩⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hA.2.1 (Ne.symm hne)) hv (hp v)

lemma F_eq (X : Complex n d) (A : Fin (d + 1) → Finset (Fin n)) (p : Fin n → Fin (d + 1))
    (hpA : ∀ v i, v ∈ A i ↔ p v = i) : F X A = X.top.filter (R p) := by
  unfold F; ext τ; simp only [Finset.mem_filter]
  refine and_congr_right fun hτ => ?_
  have hc := X.card_top τ hτ
  constructor
  · intro h
    refine ⟨hc, Finset.eq_univ_of_forall fun i => ?_⟩
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (h i)
    have : v ∈ τ ∩ A i := by rw [hv]; exact Finset.mem_singleton_self v
    rw [Finset.mem_inter] at this
    exact Finset.mem_image.mpr ⟨v, this.1, (hpA v i).mp this.2⟩
  · intro hR i
    have hi : i ∈ τ.image p := by rw [hR.2]; exact Finset.mem_univ i
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp hi
    rw [Finset.card_eq_one]
    refine ⟨v, ?_⟩
    ext u
    simp only [Finset.mem_inter, Finset.mem_singleton, hpA]
    constructor
    · rintro ⟨hu, hpu⟩; exact R_inj p hR hu hv (hpu.trans e.symm)
    · rintro rfl; exact ⟨hv, e⟩

theorem main (n d : ℕ) (hd : 1 ≤ d) (hn : d + 1 ≤ n) (X : Complex n d) :
    ∃ μ : ℝ, IsCycleEigenvalue (upLap X) μ ∧
      ∀ A : Fin (d + 1) → Finset (Fin n), IsPartition A → μ ≤ cheegerRatio X A := by
  have hinv : ∀ v ∈ cycles n d, upLap X v ∈ cycles n d := fun v _ => by
    unfold cycles upLap; rw [LinearMap.mem_ker, LinearMap.comp_apply]; exact bdLow_bdTop hd X _
  have key : ∀ x y : Form n d, inner ℝ (upLap X x) y = inner ℝ (cobdTop X x) (cobdTop X y) := by
    intro x y; unfold upLap; exact inner_bd X _ y
  have hsym : (upLap X).IsSymmetric := by
    intro x y
    calc inner ℝ (upLap X x) y = inner ℝ (cobdTop X x) (cobdTop X y) := key x y
      _ = inner ℝ (cobdTop X y) (cobdTop X x) := real_inner_comm _ _
      _ = inner ℝ (upLap X y) x := (key y x).symm
      _ = inner ℝ x (upLap X y) := real_inner_comm _ _
  have hT := hsym.restrict_invariant hinv
  have hn1 : 1 ≤ n := by omega
  let p0 : Fin n → Fin (d + 1) := fun v => ⟨min v.val d, by omega⟩
  have hsurj0 : ∀ i, ∃ v, p0 v = i := fun i =>
    ⟨⟨i.val, by omega⟩, Fin.ext (by simp only [p0]; omega)⟩
  have : Nontrivial (cycles n d) :=
    ⟨⟨⟨fT p0, fT_cycle p0 hd⟩, 0, fun h => fT_ne p0 hn1 hsurj0 (congrArg Subtype.val h)⟩⟩
  have hμ := hT.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  refine ⟨⨅ z : {z : cycles n d // z ≠ 0},
      RCLike.re (inner ℝ ((upLap X).restrict hinv z) (z : cycles n d)) / ‖(z : cycles n d)‖ ^ 2,
    ⟨x.1, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩, ?_⟩
  · have h1 := Module.End.mem_eigenspace_iff.mp hx.1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  · intro A hA
    obtain ⟨p, hpA⟩ := part_fun A hA
    have hsurj : ∀ i, ∃ v, p v = i := fun i => by
      obtain ⟨v, hv⟩ := hA.1 i; exact ⟨v, (hpA v i).mp hv⟩
    let y : cycles n d := ⟨fT p, fT_cycle p hd⟩
    have hy0 : y ≠ 0 := fun h => fT_ne p hn1 hsurj (congrArg Subtype.val h)
    have hbdd : BddBelow (Set.range fun z : {z : cycles n d // z ≠ 0} =>
        RCLike.re (inner ℝ ((upLap X).restrict hinv z) (z : cycles n d)) /
          ‖(z : cycles n d)‖ ^ 2) := by
      refine ⟨0, ?_⟩
      rintro r ⟨z, rfl⟩
      apply div_nonneg _ (sq_nonneg _)
      show 0 ≤ RCLike.re (inner ℝ (upLap X z.1.1) z.1.1)
      rw [RCLike.re_to_real, key]
      exact real_inner_self_nonneg
    refine le_trans (ciInf_le hbdd ⟨y, hy0⟩) ?_
    show RCLike.re (inner ℝ (upLap X (fT p)) (fT p)) / ‖fT p‖ ^ 2 ≤ cheegerRatio X A
    rw [RCLike.re_to_real, ← real_inner_self_eq_norm_sq, lap_fT, norm_fT, cheegerRatio,
      F_eq X A p hpA]
    have hA' : ∀ i, (A i).card = (Finset.univ.filter (fun w => p w = i)).card := fun i => by
      congr 1; ext v; simp [hpA]
    simp_rw [hA']
    have hge := card_R_ge p
    have hprod : 0 < ∏ i, ((Finset.univ.filter (fun w => p w = i)).card : ℝ) := by
      refine Finset.prod_pos fun i _ => ?_
      obtain ⟨v, hv⟩ := hsurj i
      exact_mod_cast Finset.card_pos.mpr ⟨v, by simp [hv]⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hRb : 0 < ((Finset.univ.filter (R p)).card : ℝ) := lt_of_lt_of_le hprod hge
    rw [div_le_div_iff₀ (by positivity) hprod]
    have h0 : 0 ≤ (n : ℝ) ^ 2 * ((X.top.filter (R p)).card : ℝ) := by positivity
    calc (n : ℝ) ^ 2 * ((X.top.filter (R p)).card : ℝ) *
          ∏ i, ((Finset.univ.filter (fun w => p w = i)).card : ℝ)
        ≤ (n : ℝ) ^ 2 * ((X.top.filter (R p)).card : ℝ) * ((Finset.univ.filter (R p)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hge h0
      _ = (n : ℝ) * ((X.top.filter (R p)).card : ℝ) * ((n : ℝ) * ((Finset.univ.filter (R p)).card : ℝ)) := by
          ring

end SimplicialIso.Cheeger.Aux17

open SimplicialIso.Cheeger in
theorem solution (n d : ℕ) (hd : 1 ≤ d) (hn : d + 1 ≤ n) (X : Complex n d) :
    ∃ μ : ℝ, IsCycleEigenvalue (upLap X) μ ∧
      ∀ A : Fin (d + 1) → Finset (Fin n), IsPartition A → μ ≤ cheegerRatio X A := by
  exact SimplicialIso.Cheeger.Aux17.main n d hd hn X
