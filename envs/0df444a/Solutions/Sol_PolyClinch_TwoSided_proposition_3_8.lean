-- Prove2me | solution 1 for PolyClinch.TwoSided.proposition_3_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T03:42:19.753603+00:00
-- url     : https://prove2.me/submissions/714991bf-a4b7-4712-9610-0feaf31e7ac3

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Market
import Definitions.Def_PolyClinch_TwoSided_Clinching

open PolyClinch.TwoSided Finset

namespace PolyClinchProp38Sol

/-- Per-buyer invariant of Algorithm 2. -/
def InvOne (B : WithTop ℝ) (v c p : ℝ) (d : WithTop ℝ) : Prop :=
  0 ≤ c ∧ 0 ≤ d ∧ ((p : ℝ) : WithTop ℝ) ≤ B ∧
    (∀ r : ℝ, d = (r : WithTop ℝ) → ((p + c * r : ℝ) : WithTop ℝ) ≤ B) ∧
    (d = ⊤ → c = 0 ∨ B = ⊤) ∧ (v ≤ c → 0 < c → d = 0)

lemma invOne_demandUpdate (B : WithTop ℝ) (v c p : ℝ) (hc : 0 ≤ c)
    (hp : ((p : ℝ) : WithTop ℝ) ≤ B) : InvOne B v c p (demandUpdate B p c v) := by
  unfold demandUpdate
  by_cases hcv : c < v
  · rw [if_pos hcv]
    by_cases hc0 : c = 0
    · rw [if_pos hc0]
      exact ⟨hc, le_top, hp, fun r hr => (WithTop.top_ne_coe hr).elim, fun _ => Or.inl hc0,
        fun h _ => absurd hcv (not_lt.mpr h)⟩
    · rw [if_neg hc0]
      have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      induction B using WithTop.recTopCoe with
      | top =>
        refine ⟨hc, le_top, hp, fun r hr => ?_, fun _ => Or.inr rfl,
          fun h _ => absurd hcv (not_lt.mpr h)⟩
        simp at hr
      | coe b =>
        have hpb : p ≤ b := WithTop.coe_le_coe.mp hp
        simp only [WithTop.map_coe]
        refine ⟨hc, ?_, hp, fun r hr => ?_, fun h => ?_, fun h _ => absurd hcv (not_lt.mpr h)⟩
        · exact WithTop.coe_le_coe.mpr (div_nonneg (by linarith) hc)
        · have hr' : (b - p) / c = r := WithTop.coe_injective hr
          rw [← hr']
          have : p + c * ((b - p) / c) = b := by field_simp; ring
          rw [this]
        · exact absurd h WithTop.coe_ne_top
  · rw [if_neg hcv]
    refine ⟨hc, le_refl _, hp, fun r hr => ?_, fun h => ?_, fun _ _ => rfl⟩
    · have : r = 0 := by exact_mod_cast hr.symm
      subst this
      simpa using hp
    · exact absurd h (by simp)

lemma invOne_clinch {B : WithTop ℝ} {v c p : ℝ} {d : WithTop ℝ} (h : InvOne B v c p d)
    {s : ℝ} (_hs : 0 ≤ s) (hsd : ((s : ℝ) : WithTop ℝ) ≤ d) :
    ((p + c * s : ℝ) : WithTop ℝ) ≤ B := by
  obtain ⟨hc, -, hp, hr, htop, -⟩ := h
  induction d using WithTop.recTopCoe with
  | top =>
    rcases htop rfl with h0 | hB
    · subst h0; simpa using hp
    · rw [hB]; exact le_top
  | coe r =>
    have hsr : s ≤ r := WithTop.coe_le_coe.mp hsd
    have h1 := hr r rfl
    induction B using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      have h2 := WithTop.coe_le_coe.mp h1
      have h3 : c * s ≤ c * r := mul_le_mul_of_nonneg_left hsr hc
      exact WithTop.coe_le_coe.mpr (by linarith)

variable {n m : ℕ} (E : Finset (Fin n × Fin m))

/-- Invariant of Algorithm 2 (for fixed clocks `c`). -/
def Inv (I : PublicInfo E) (c : Fin (n + m) → ℝ) (w : ↥(extEdges E) → ℝ)
    (p : Fin (n + m) → ℝ) (d : Fin (n + m) → WithTop ℝ) : Prop :=
  w ∈ extP E I ∧ ∀ k, InvOne (extBudget E I k) (extBid E I k) (c k) (p k) (d k)

lemma clinch_facts (I : PublicInfo E) (w : ↥(extEdges E) → ℝ) (hw : w ∈ extP E I)
    (d : Fin (n + m) → WithTop ℝ) (hd : ∀ k, 0 ≤ d k) (i : Fin (n + m))
    (ξ : ↥(extEdges E) → ℝ) (hξ : ξ ∈ clinchingPolytope E I w d i) :
    w + ξ ∈ extP E I ∧ ((∑ e ∈ extEdgesOfBuyer E i, ξ e : ℝ) : WithTop ℝ) ≤ d i ∧
      (∀ e, 0 ≤ ξ e) := by
  obtain ⟨hξ0, hξoff, hξeq⟩ := hξ
  have h0 : (0 : {k : Fin (n + m) // k ≠ i} → ℝ) ∈ remnantSupplyOthers2 E I w d i 0 := by
    refine ⟨fun _ => le_refl _, 0, ⟨fun _ => le_refl _, by simpa using hw, fun k => ?_⟩,
      fun _ _ => rfl, fun k => by simp⟩
    simpa using hd k
  rw [← hξeq] at h0
  obtain ⟨-, x, ⟨hx0, hxP, hxd⟩, hxi, hxk⟩ := h0
  have hxξ : x = ξ := by
    funext e
    by_cases he : e ∈ extEdgesOfBuyer E i
    · exact hxi e he
    · rw [hξoff e he]
      have hne : e.1.1 ≠ i := by
        intro h; apply he; simp [extEdgesOfBuyer, h]
      have hsum := hxk ⟨e.1.1, hne⟩
      simp only [Pi.zero_apply] at hsum
      have hmem : e ∈ extEdgesOfBuyer E e.1.1 := by simp [extEdgesOfBuyer]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hx0 e)).mp hsum e hmem
  subst hxξ
  exact ⟨hxP, hxd i, hx0⟩

lemma zero_mem_extP (I : PublicInfo E) (hf : ∀ j, IsMonoSubmodOn (edgesOfSeller E j) (I.f j)) :
    (0 : ↥(extEdges E) → ℝ) ∈ extP E I := by
  refine ⟨fun _ => le_refl _, fun j => ⟨fun _ _ => le_refl _, fun F hF => ?_⟩⟩
  simp only [Pi.zero_apply, Finset.sum_const_zero]
  obtain ⟨h0, hmono, -⟩ := hf j
  unfold extF
  split_ifs
  · rw [← h0]; exact hmono _ _ (Finset.empty_subset _) (subset_refl _)
  · rw [← h0]
    refine hmono _ _ (Finset.empty_subset _) ?_
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    have := hF he
    simp [extEdgesOfSeller, edgesOfSeller, liftEdge] at this ⊢
    exact this

lemma extBudget_nonneg (I : PublicInfo E) (hB : ∀ i, 0 ≤ I.budget i) (k : Fin (n + m)) :
    (0 : WithTop ℝ) ≤ extBudget E I k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [extBudget, hB i]
  · simp [extBudget]

lemma finRotate_val : ∀ (N : ℕ) (x : Fin N), ((finRotate N x : Fin N) : ℕ) = ((x : ℕ) + 1) % N
  | 0, x => x.elim0
  | N + 1, x => by
    rw [finRotate_apply, Fin.val_add]
    rcases N with _ | N
    · simp
    · simp

lemma liftEdge_inj : Function.Injective (liftEdge E) := by
  intro a b h
  have h1 := congrArg (fun x : ↥(extEdges E) => x.1) h
  simp only [liftEdge, Prod.mk.injEq] at h1
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.castAdd_inj.mp h1.1
  · exact h1.2

lemma inv_clinch_pres (I : PublicInfo E) (c : Fin (n + m) → ℝ) (i : Fin (n + m))
    (u u' : Alg2Inner E) (h : Alg2Clinch E I c i u u') (hu : Inv E I c u.w u.p u.d) :
    Inv E I c u'.w u'.p u'.d := by
  obtain ⟨ξ, hξ, hw, hp, hd, -⟩ := h
  have hd0 : ∀ k, 0 ≤ u.d k := fun k => (hu.2 k).2.1
  obtain ⟨hwξ, hsd, hξ0⟩ := clinch_facts E I u.w hu.1 u.d hd0 i ξ hξ.prop
  have hs0 : 0 ≤ ∑ e ∈ extEdgesOfBuyer E i, ξ e := Finset.sum_nonneg (fun e _ => hξ0 e)
  have hpB := invOne_clinch (hu.2 i) hs0 hsd
  refine ⟨by rw [hw]; exact hwξ, fun k => ?_⟩
  rw [hd, hp]
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self]
    exact invOne_demandUpdate _ _ _ _ (hu.2 k).1 hpB
  · simp only [Function.update_of_ne hk]
    exact hu.2 k

lemma inv_tick (I : PublicInfo E) (ε : ℝ) (hε : 0 < ε) (c : Fin (n + m) → ℝ)
    (w : ↥(extEdges E) → ℝ) (p : Fin (n + m) → ℝ) (d : Fin (n + m) → WithTop ℝ)
    (l : Fin (n + m)) (h : Inv E I c w p d) :
    Inv E I (Function.update c l (c l + ε)) w p
      (Function.update d l (demandUpdate (extBudget E I l) (p l) (c l + ε) (extBid E I l))) := by
  refine ⟨h.1, fun k => ?_⟩
  by_cases hk : k = l
  · subst hk
    simp only [Function.update_self]
    exact invOne_demandUpdate _ _ _ _ (by linarith [(h.2 k).1]) (h.2 k).2.2.1
  · simp only [Function.update_of_ne hk]
    exact h.2 k

lemma virt_buyer_eq (j : Fin m) (e : ↥(extEdges E)) (he : e.1.1 = Fin.natAdd n j) :
    e = virtEdge E j := by
  obtain ⟨⟨b, j'⟩, hmem⟩ := e
  simp only at he
  subst he
  simp only [extEdges, mem_union, mem_image] at hmem
  rcases hmem with ⟨a, _, h⟩ | ⟨j'', _, h⟩
  · exfalso
    have h1 := congrArg (fun x => (x.1 : ℕ)) h
    simp at h1
    have := a.1.isLt
    omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hv := congrArg Fin.val h1
    simp at hv
    have hj : j'' = j := Fin.ext hv
    apply Subtype.ext
    simp only [virtEdge]
    rw [← h2, hj]

lemma sum_virt_buyer (j : Fin m) (g : ↥(extEdges E) → ℝ) :
    ∑ e ∈ extEdgesOfBuyer E (Fin.natAdd n j), g e = g (virtEdge E j) := by
  have : extEdgesOfBuyer E (Fin.natAdd n j) = {virtEdge E j} := by
    ext e
    simp only [extEdgesOfBuyer, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact virt_buyer_eq E j e
    · rintro rfl; rfl
  rw [this, sum_singleton]

lemma virt_not_mem_map (j : Fin m) (F : Finset ↥E) :
    virtEdge E j ∉ F.map ⟨liftEdge E, liftEdge_inj E⟩ := by
  intro hx
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
  obtain ⟨a, -, ha⟩ := hx
  have h2 := congrArg (fun x : ↥(extEdges E) => (x.1.1 : ℕ)) ha
  simp [liftEdge, virtEdge] at h2
  have := a.1.1.isLt
  omega

lemma sum_extSeller (j : Fin m) (g : ↥(extEdges E) → ℝ) :
    ∑ e ∈ extEdgesOfSeller E j, g e =
      g (virtEdge E j) + ∑ e ∈ edgesOfSeller E j, g (liftEdge E e) := by
  have hset : extEdgesOfSeller E j =
      insert (virtEdge E j) ((edgesOfSeller E j).map ⟨liftEdge E, liftEdge_inj E⟩) := by
    ext e
    simp only [extEdgesOfSeller, edgesOfSeller, mem_filter, mem_univ, true_and, mem_insert,
      mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro he
      obtain ⟨⟨b, j'⟩, hmem⟩ := e
      simp only at he
      subst he
      have hmem' := hmem
      simp only [extEdges, mem_union, mem_image] at hmem'
      rcases hmem' with ⟨a, ha, h⟩ | ⟨j'', _, h⟩
      · right
        simp only [Prod.mk.injEq] at h
        refine ⟨⟨a, ha⟩, h.2, ?_⟩
        apply Subtype.ext
        simp only [liftEdge, Prod.mk.injEq]
        exact h
      · left
        simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        apply Subtype.ext
        simp only [virtEdge, Prod.mk.injEq]
        rw [← h1, h2]
        simp
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · rfl
      · simpa [liftEdge] using ha
  rw [hset, sum_insert (virt_not_mem_map E j _), sum_map]
  rfl

lemma blocked (I : PublicInfo E) (w : ↥(extEdges E) → ℝ) (hw : w ∈ extP E I)
    (d : Fin (n + m) → WithTop ℝ) (hd : ∀ k, 0 ≤ d k) (j : Fin m)
    (hdj : d (Fin.natAdd n j) = ⊤) (i : Fin (n + m)) (hi : i ≠ Fin.natAdd n j)
    (ξ : ↥(extEdges E) → ℝ) (hξ : ξ ∈ clinchingPolytope E I w d i) :
    ∀ e ∈ edgesOfSeller E j, ξ (liftEdge E e) = 0 := by
  obtain ⟨_, hξoff, hξeq⟩ := hξ
  have hvS : virtEdge E j ∈ extEdgesOfSeller E j := by simp [extEdgesOfSeller, virtEdge]
  have hFtop : extF E I j (extEdgesOfSeller E j) = I.f j (edgesOfSeller E j) := by
    unfold extF; rw [if_pos hvS]
  set slack := I.f j (edgesOfSeller E j) - ∑ e ∈ extEdgesOfSeller E j, w e with hslack
  have hslack0 : 0 ≤ slack := by
    have := (hw.2 j).2 _ (subset_refl _)
    rw [hFtop] at this
    linarith
  let x0 : ↥(extEdges E) → ℝ := fun e => if e = virtEdge E j then slack else 0
  have hx0nn : ∀ e, 0 ≤ x0 e := fun e => by
    simp only [x0]; split_ifs <;> linarith
  have hsumx0 : ∀ F : Finset ↥(extEdges E),
      ∑ e ∈ F, x0 e = if virtEdge E j ∈ F then slack else 0 := by
    intro F; simp only [x0]; rw [Finset.sum_ite_eq']
  have hx0R : x0 ∈ remnantSupply2 E I w d := by
    refine ⟨hx0nn, ⟨fun e => add_nonneg (hw.1 e) (hx0nn e),
      fun j' => ⟨fun e _ => add_nonneg (hw.1 e) (hx0nn e), fun F hF => ?_⟩⟩, fun k => ?_⟩
    · simp only [Pi.add_apply, sum_add_distrib, hsumx0]
      split_ifs with hv
      · have hj : j = j' := by
          have := hF hv
          simpa [extEdgesOfSeller, virtEdge] using this
        subst hj
        have h1 : ∑ e ∈ F, w e ≤ ∑ e ∈ extEdgesOfSeller E j, w e :=
          sum_le_sum_of_subset_of_nonneg hF (fun e _ _ => hw.1 e)
        have h2 : extF E I j F = I.f j (edgesOfSeller E j) := by
          unfold extF; rw [if_pos hv]
        rw [h2]
        linarith
      · rw [add_zero]
        exact (hw.2 j').2 F hF
    · rw [hsumx0]
      split_ifs with hv
      · have : k = Fin.natAdd n j := by
          simp [extEdgesOfBuyer, virtEdge] at hv
          exact hv.symm
        subst this
        rw [hdj]
        exact le_top
      · simpa using hd k
  have hu0 : (fun k : {k : Fin (n + m) // k ≠ i} => ∑ e ∈ extEdgesOfBuyer E k, x0 e) ∈
      remnantSupplyOthers2 E I w d i 0 := by
    refine ⟨fun k => sum_nonneg (fun e _ => hx0nn e), x0, hx0R, fun e he => ?_, fun k => rfl⟩
    have : e ≠ virtEdge E j := by
      rintro rfl
      apply hi
      simp [extEdgesOfBuyer, virtEdge] at he
      exact he.symm
    simp [x0, this]
  rw [← hξeq] at hu0
  obtain ⟨-, x, ⟨hx0, hxP, -⟩, hxi, hxk⟩ := hu0
  have hxv : x (virtEdge E j) = slack := by
    have := hxk ⟨Fin.natAdd n j, Ne.symm hi⟩
    simp only at this
    rw [sum_virt_buyer, sum_virt_buyer] at this
    simpa [x0] using this
  have hineq := (hxP.2 j).2 _ (subset_refl _)
  rw [hFtop] at hineq
  simp only [Pi.add_apply, sum_add_distrib] at hineq
  rw [sum_extSeller E j x, hxv] at hineq
  have hsum0 : ∑ e ∈ edgesOfSeller E j, x (liftEdge E e) ≤ 0 := by linarith
  have hz := (sum_eq_zero_iff_of_nonneg (fun e _ => hx0 (liftEdge E e))).mp
    (le_antisymm hsum0 (sum_nonneg fun e _ => hx0 _))
  intro e he
  by_cases hle : liftEdge E e ∈ extEdgesOfBuyer E i
  · rw [← hxi _ hle]; exact hz e he
  · exact hξoff _ hle

/-- The quantity `r_j + Δr_j − p_{n+j} − ρ_j w(E_j)` whose nonnegativity is (IRs). -/
def Phi (I : PublicInfo E) (j : Fin m) (R dr : ℝ) (p : Fin (n + m) → ℝ)
    (w : ↥(extEdges E) → ℝ) : ℝ :=
  R + dr - p (Fin.natAdd n j) - I.rho j * ∑ e ∈ edgesOfSeller E j, w (liftEdge E e)

lemma phi_clinch (I : PublicInfo E) (j : Fin m) (_hρ : 0 ≤ I.rho j) (c : Fin (n + m) → ℝ)
    (i : Fin (n + m)) (u u' : Alg2Inner E) (h : Alg2Clinch E I c i u u')
    (hu : Inv E I c u.w u.p u.d) (R : ℝ)
    (H : (∃ i0 : Fin n, i = Fin.castAdd m i0) → u.d (Fin.natAdd n j) = ⊤ ∨ I.rho j ≤ c i) :
    Phi E I j R (u.dr j) u.p u.w ≤ Phi E I j R (u'.dr j) u'.p u'.w := by
  obtain ⟨ξ, hξ, hw, hp, -, hdr⟩ := h
  have hd0 : ∀ k, 0 ≤ u.d k := fun k => (hu.2 k).2.1
  obtain ⟨-, -, hξ0⟩ := clinch_facts E I u.w hu.1 u.d hd0 i ξ hξ.prop
  have hξoff := hξ.prop.2.1
  have hvpart : c (virtEdge E j).1.1 * ξ (virtEdge E j) -
      (Function.update u.p i (u.p i + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e) (Fin.natAdd n j) -
        u.p (Fin.natAdd n j)) = 0 := by
    by_cases hi : i = Fin.natAdd n j
    · subst hi
      rw [Function.update_self, sum_virt_buyer]
      simp only [virtEdge]
      ring
    · rw [Function.update_of_ne (Ne.symm hi)]
      have : ξ (virtEdge E j) = 0 := hξoff _ (by
        simp only [extEdgesOfBuyer, mem_filter, mem_univ, true_and, virtEdge]
        exact Ne.symm hi)
      rw [this]
      ring
  have hreal : ∑ e ∈ edgesOfSeller E j, I.rho j * ξ (liftEdge E e) ≤
      ∑ e ∈ edgesOfSeller E j, c (liftEdge E e).1.1 * ξ (liftEdge E e) := by
    apply sum_le_sum
    intro e he
    by_cases h0 : ξ (liftEdge E e) = 0
    · rw [h0]; simp
    · have hmem : liftEdge E e ∈ extEdgesOfBuyer E i := by
        by_contra hc; exact h0 (hξoff _ hc)
      have hi : (liftEdge E e).1.1 = i := by simpa [extEdgesOfBuyer] using hmem
      have hreal : ∃ i0 : Fin n, i = Fin.castAdd m i0 := ⟨e.1.1, by rw [← hi]; rfl⟩
      rcases H hreal with htop | hle
      · exfalso
        apply h0
        refine blocked E I u.w hu.1 u.d hd0 j htop i ?_ ξ hξ.prop e he
        rw [← hi]
        intro h
        have := congrArg Fin.val h
        simp [liftEdge] at this
        have := e.1.1.isLt
        omega
      · rw [hi]
        exact mul_le_mul_of_nonneg_right hle (hξ0 _)
  rw [← mul_sum] at hreal
  unfold Phi
  rw [hw, hp, hdr]
  simp only [Pi.add_apply, sum_add_distrib]
  rw [sum_extSeller E j (fun e => c e.1.1 * ξ e)]
  linarith

/-- Round-robin clocks: `c_k = ε (a + [k < l])`. -/
def ClockForm (ε : ℝ) (c : Fin (n + m) → ℝ) (l : Fin (n + m)) : Prop :=
  ∃ a : ℕ, ∀ k : Fin (n + m), c k = ε * ((a : ℝ) + if (k : ℕ) < (l : ℕ) then 1 else 0)

omit E in
lemma clock_anti {ε : ℝ} (hε : 0 ≤ ε) {c : Fin (n + m) → ℝ} {l : Fin (n + m)}
    (h : ClockForm ε c l) {k k' : Fin (n + m)} (hkk : (k : ℕ) ≤ k') : c k' ≤ c k := by
  obtain ⟨a, ha⟩ := h
  rw [ha, ha]
  apply mul_le_mul_of_nonneg_left _ hε
  have : (if (k' : ℕ) < l then (1 : ℝ) else 0) ≤ if (k : ℕ) < l then 1 else 0 := by
    split_ifs <;> first | (exfalso; omega) | norm_num
  linarith

omit E in
lemma clock_step {ε : ℝ} {c : Fin (n + m) → ℝ} {l : Fin (n + m)} (h : ClockForm ε c l) :
    ClockForm ε (Function.update c l (c l + ε)) (finRotate _ l) := by
  obtain ⟨a, ha⟩ := h
  by_cases hl : (l : ℕ) + 1 < n + m
  · refine ⟨a, fun k => ?_⟩
    have hrot : ((finRotate _ l : Fin (n + m)) : ℕ) = l + 1 := by
      rw [finRotate_val, Nat.mod_eq_of_lt hl]
    rw [hrot]
    by_cases hk : k = l
    · subst hk
      rw [Function.update_self, ha]
      simp
      ring
    · rw [Function.update_of_ne hk, ha]
      have hkl : (k : ℕ) ≠ l := fun h => hk (Fin.ext h)
      have : ((k : ℕ) < l + 1) ↔ ((k : ℕ) < l) := by omega
      simp only [this]
  · refine ⟨a + 1, fun k => ?_⟩
    have hrot : ((finRotate _ l : Fin (n + m)) : ℕ) = 0 := by
      rw [finRotate_val]
      have : (l : ℕ) + 1 = n + m := by have := l.isLt; omega
      rw [this, Nat.mod_self]
    rw [hrot]
    simp only [Nat.not_lt_zero, if_false, add_zero]
    by_cases hk : k = l
    · subst hk
      rw [Function.update_self, ha]
      simp
      ring
    · rw [Function.update_of_ne hk, ha]
      have : (k : ℕ) < l := by
        have : (k : ℕ) ≠ l := fun h => hk (Fin.ext h)
        have := k.isLt
        omega
      simp [this]

lemma dU_top_ne (p c v : ℝ) (h : demandUpdate ⊤ p c v ≠ ⊤) : v ≤ c := by
  unfold demandUpdate at h
  by_contra hlt
  push Not at hlt
  rw [if_pos hlt] at h
  split_ifs at h <;> simp_all

lemma extBudget_virt (I : PublicInfo E) (j : Fin m) : extBudget E I (Fin.natAdd n j) = ⊤ := by
  simp [extBudget]

lemma extBid_virt (I : PublicInfo E) (j : Fin m) : extBid E I (Fin.natAdd n j) = I.rho j := by
  simp [extBid]

/-- State invariant of Algorithm 2 used for (IRs). -/
def SInv (I : PublicInfo E) (ε : ℝ) (s : Alg2State E) : Prop :=
  Inv E I s.c s.w s.p s.d ∧ ClockForm ε s.c s.l ∧
    (∀ j, s.d (Fin.natAdd n j) ≠ ⊤ → I.rho j ≤ s.c (Fin.natAdd n j)) ∧
    ∀ j, 0 ≤ Phi E I j (s.r j) 0 s.p s.w

lemma sinv_step (I : PublicInfo E) (hρ : ∀ j, 0 ≤ I.rho j) (ε : ℝ) (hε : 0 < ε)
    (s s' : Alg2State E) (h : Alg2Step E I ε s s') (hs : SInv E I ε s) : SInv E I ε s' := by
  obtain ⟨hinv, hclock, hvirt, hphi⟩ := hs
  obtain ⟨u, hu0, hcl, hw, hp, hr, hc, hd, hl⟩ := h
  have key : ∀ N ≤ n + m, Inv E I s.c (u N).w (u N).p (u N).d ∧
      (∀ k : Fin (n + m), (k : ℕ) < N →
        (u N).d k = demandUpdate (extBudget E I k) ((u N).p k) (s.c k) (extBid E I k)) ∧
      (∀ k : Fin (n + m), N ≤ (k : ℕ) → (u N).d k = s.d k) ∧
      ∀ j, Phi E I j (s.r j) 0 s.p s.w ≤ Phi E I j (s.r j) ((u N).dr j) (u N).p (u N).w := by
    intro N
    induction N with
    | zero =>
      intro _
      rw [hu0]
      exact ⟨hinv, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ _ => rfl, fun j => le_refl _⟩
    | succ N ih =>
      intro hN
      obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
      have hclN := hcl N (by omega)
      refine ⟨inv_clinch_pres E I s.c _ _ _ hclN h1, fun k hk => ?_, fun k hk => ?_,
        fun j => (h4 j).trans (phi_clinch E I j (hρ j) s.c _ _ _ hclN h1 (s.r j) ?_)⟩
      · obtain ⟨ξ, -, -, hp', hd', -⟩ := hclN
        rw [hd']
        by_cases hkN : k = ⟨N, by omega⟩
        · rw [hkN, Function.update_self]
        · have hkN' : (k : ℕ) < N := by
            have : (k : ℕ) ≠ N := fun h => hkN (Fin.ext h)
            omega
          rw [Function.update_of_ne hkN, h2 k hkN', hp', Function.update_of_ne hkN]
      · obtain ⟨ξ, -, -, -, hd', -⟩ := hclN
        have hkN : k ≠ ⟨N, by omega⟩ := fun h => by rw [h] at hk; simp at hk
        rw [hd', Function.update_of_ne hkN, h3 k (by omega)]
      · rintro ⟨i0, hi0⟩
        have hi0' := congrArg Fin.val hi0
        simp at hi0'
        have hvN : N ≤ ((Fin.natAdd n j : Fin (n + m)) : ℕ) := by simp; omega
        rw [h3 _ hvN]
        by_cases htop : s.d (Fin.natAdd n j) = ⊤
        · exact Or.inl htop
        · right
          exact (hvirt j htop).trans (clock_anti hε.le hclock (by simp; omega))
  obtain ⟨h1, h2, -, h4⟩ := key (n + m) le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd, hw, hp, hc, Function.update_self]
    exact inv_tick E I ε hε s.c (u (n + m)).w (u (n + m)).p (u (n + m)).d s.l h1
  · rw [hc, hl]
    exact clock_step hclock
  · intro j hne
    rw [hd, hp, hc] at hne
    rw [hc]
    by_cases hj : Fin.natAdd n j = s.l
    · rw [← hj] at hne ⊢
      simp only [Function.update_self, extBudget_virt, extBid_virt] at hne ⊢
      exact dU_top_ne _ _ _ hne
    · rw [Function.update_of_ne hj] at hne ⊢
      rw [h2 _ (Fin.natAdd n j).isLt] at hne
      simp only [extBudget_virt, extBid_virt] at hne
      exact dU_top_ne _ _ _ hne
  · intro j
    rw [hr, hp, hw]
    have := h4 j
    have := hphi j
    unfold Phi at *
    simp only [Pi.add_apply]
    linarith

end PolyClinchProp38Sol

open PolyClinchProp38Sol in
theorem solution {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (A : Allocation E) (hA : Mech2Outcome E I ε A) :
    ∀ j, I.rho j * I.f j (edgesOfSeller E j) ≤ sellerUtility E I A j := by
  obtain ⟨-, hB, hrho, hf⟩ := hI
  have hρ : ∀ j, 0 ≤ I.rho j := fun j => by
    obtain ⟨k, hk⟩ := hrho j
    rw [hk]
    positivity
  obtain ⟨S, ⟨T, s, hinit, hrun, _, rfl⟩, rfl⟩ := hA
  have h0 : SInv E I ε (s 0) := by
    obtain ⟨hw, hp, hr, hc, hd, hl⟩ := hinit
    refine ⟨?_, ⟨0, fun k => ?_⟩, fun j h => ?_, fun j => ?_⟩
    · rw [hw, hp, hc, hd]
      refine ⟨zero_mem_extP E I hf, fun k => ⟨le_refl _, le_top, ?_, fun r hr => ?_,
        fun _ => Or.inl rfl, fun _ h => absurd h (lt_irrefl 0)⟩⟩
      · simpa using extBudget_nonneg E I hB k
      · simp at hr
    · rw [hc, hl]
      simp
    · rw [hd] at h
      exact absurd rfl h
    · unfold Phi
      rw [hr, hp, hw]
      simp
  have hall : ∀ t ≤ T, SInv E I ε (s t) := by
    intro t
    induction t with
    | zero => intro _; exact h0
    | succ t ih =>
      intro ht
      exact sinv_step E I hρ ε hε _ _ (hrun t (by omega)).2 (ih (by omega))
  intro j
  have := (hall T le_rfl).2.2.2 j
  unfold Phi at this
  simp only [sellerUtility, toOriginal]
  linarith
