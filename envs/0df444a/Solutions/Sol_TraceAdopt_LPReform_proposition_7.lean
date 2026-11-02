-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:48:26.626414+00:00
-- url     : https://prove2.me/submissions/c0c32231-0488-4847-b8b5-f3a57e148ae4

import Definitions.Def_TraceAdopt_LPReform_BiLP4
import Definitions.Def_TraceAdopt_LPReform_BiLP5

namespace TAChordal

open SimpleGraph

variable {V T : Type} [DecidableEq V] [DecidableEq T] {t : SimpleGraph T} (ht : t.IsTree) (X : T → Finset V)
include ht

theorem path_eq {x y : T} (p q : t.Walk x y) (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  congrArg Subtype.val ((ht.isAcyclic.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)

/-- The unique path to the root. -/
noncomputable def P (r : T) (x : T) : t.Walk x r := (ht.connected.preconnected x r).some.bypass

theorem P_isPath (r x : T) : (P ht r x).IsPath := Walk.bypass_isPath _

theorem P_unique (r x : T) (p : t.Walk x r) (hp : p.IsPath) : p = P ht r x :=
  path_eq ht p _ hp (P_isPath ht r x)

variable (hiii : ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support →
    X s ∩ X s'' ⊆ X s')
include hiii

theorem convex {v : V} {a b : T} (ha : v ∈ X a) (hb : v ∈ X b) (p : t.Walk a b) (hp : p.IsPath) :
    ∀ c ∈ p.support, v ∈ X c :=
  fun c hc => hiii a c b p hp hc (Finset.mem_inter.2 ⟨ha, hb⟩)

/-- The `P`-minimal node of the subtree of `v` lies on the root path of every node of it. -/
theorem F (r : T) (v : V) (z y : T) (hz : v ∈ X z)
    (hmin : ∀ w, v ∈ X w → (P ht r z).length ≤ (P ht r w).length) (hy : v ∈ X y) :
    z ∈ (P ht r y).support := by
  classical
  obtain ⟨q0⟩ := ht.connected.preconnected y z
  set q := q0.bypass with hqdef
  have hq : q.IsPath := Walk.bypass_isPath _
  have hqN : ∀ c ∈ q.support, v ∈ X c := convex ht X hiii hy hz q hq
  by_cases hzr : z = r
  · subst hzr; exact Walk.end_mem_support _
  -- decompose the root path of `z`
  have hPz := P_isPath ht r z
  generalize hPdef : P ht r z = Pz at hPz hmin
  cases Pz with
  | nil => exact absurd rfl hzr
  | @cons _ z' _ hadj rest =>
    have hrest : rest.IsPath := hPz.of_cons
    have hzrest : z ∉ rest.support := ((Walk.cons_isPath_iff hadj rest).1 hPz).2
    have hPz' : P ht r z' = rest := (P_unique ht r z' rest hrest).symm
    -- the parent of `z` is outside the subtree of `v`
    have hz'N : v ∉ X z' := by
      intro h
      have := hmin z' h
      rw [hPz', Walk.length_cons] at this
      omega
    -- the root path of `z` meets the subtree of `v` only at `z`
    have honly : ∀ w ∈ rest.support, v ∉ X w := by
      intro w hw hvw
      have hpath : (Walk.cons hadj (rest.takeUntil w hw)).IsPath := by
        rw [Walk.cons_isPath_iff]
        exact ⟨hrest.takeUntil hw, fun h => hzrest (rest.support_takeUntil_subset_support hw h)⟩
      apply hz'N
      apply convex ht X hiii hz hvw _ hpath
      simp
    have happ : (q.append (Walk.cons hadj rest)).IsPath := by
      rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
        List.nodup_append]
      refine ⟨(Walk.isPath_def _).1 hq, (Walk.isPath_def _).1 hrest, ?_⟩
      intro a ha b hb hab
      subst hab
      exact honly a hb (hqN a ha)
    have := P_unique ht r y _ happ
    rw [← this]
    exact (Walk.mem_support_append_iff _ _).2 (Or.inl (Walk.end_mem_support _))

/-- Comparison of two nodes on a root path. -/
theorem order (r : T) (y z zu : T) (hz : z ∈ (P ht r y).support) (hzu : zu ∈ (P ht r y).support)
    (hlen : (P ht r zu).length ≤ (P ht r z).length) :
    z ∈ ((P ht r y).takeUntil zu hzu).support := by
  classical
  have hspec := Walk.take_spec (P ht r y) hzu
  have hdrop : (P ht r y).dropUntil zu hzu = P ht r zu :=
    P_unique ht r zu _ ((P_isPath ht r y).dropUntil hzu)
  have hz' : z ∈ (((P ht r y).takeUntil zu hzu).append ((P ht r y).dropUntil zu hzu)).support := by
    rw [hspec]; exact hz
  rcases (Walk.mem_support_append_iff _ _).1 hz' with h | h
  · exact h
  · rw [hdrop] at h
    have hspec2 := Walk.take_spec (P ht r zu) h
    have hdrop2 : (P ht r zu).dropUntil z h = P ht r z :=
      P_unique ht r z _ ((P_isPath ht r zu).dropUntil h)
    have hl : (P ht r zu).length = ((P ht r zu).takeUntil z h).length + (P ht r z).length := by
      conv_lhs => rw [← hspec2]
      rw [Walk.length_append, hdrop2]
    have h0 : ((P ht r zu).takeUntil z h).length = 0 := by omega
    have := Walk.eq_of_length_eq_zero h0
    subst this
    exact Walk.end_mem_support _

/-- Existence of a simplicial vertex relative to a finite set. -/
theorem simplicial [Fintype T] (U : Finset V) (hU : U.Nonempty) (hcov : ∀ v ∈ U, ∃ y, v ∈ X y) :
    ∃ v ∈ U, ∃ z, v ∈ X z ∧ ∀ u ∈ U, ∀ y, u ∈ X y → v ∈ X y → u ∈ X z := by
  classical
  have hne : Nonempty T := ht.connected.nonempty
  let r : T := Classical.arbitrary T
  have hzv : ∀ v ∈ U, ∃ z, v ∈ X z ∧ ∀ w, v ∈ X w → (P ht r z).length ≤ (P ht r w).length := by
    intro v hv
    obtain ⟨y0, hy0⟩ := hcov v hv
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun w => v ∈ X w))
      (fun w => (P ht r w).length) ⟨y0, by simp [hy0]⟩
    refine ⟨z, by simpa using hz, fun w hw => hmin w (by simp [hw])⟩
  choose! zv hzvX hzvmin using hzv
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image U (fun v => (P ht r (zv v)).length) hU
  refine ⟨v, hv, zv v, hzvX v hv, ?_⟩
  intro u hu y huy hvy
  have h1 := F ht X hiii r v (zv v) y (hzvX v hv) (hzvmin v hv) hvy
  have h2 := F ht X hiii r u (zv u) y (hzvX u hu) (hzvmin u hu) huy
  have h3 := order ht X hiii r y (zv v) (zv u) h1 h2 (hvmax u hu)
  exact hiii y (zv v) (zv u) _ ((P_isPath ht r y).takeUntil h2) h3
    (Finset.mem_inter.2 ⟨huy, hzvX u hu⟩)

/-- No nonempty set in which every vertex has an in-neighbour along a bag-pair. -/
theorem noBad [Fintype T] (ℓ : V → V → ℕ)
    (h1 : ∀ z, ∀ u ∈ X z, ∀ v ∈ X z, u ≠ v → ℓ u v + ℓ v u = 1)
    (h2 : ∀ z, ∀ u ∈ X z, ∀ v ∈ X z, ∀ x ∈ X z, u ≠ v → v ≠ x → u ≠ x →
      ℓ u v + ℓ v x + ℓ x u ≤ 2) :
    ∀ U : Finset V, U.Nonempty →
      (∀ v ∈ U, ∃ u ∈ U, u ≠ v ∧ (∃ y, u ∈ X y ∧ v ∈ X y) ∧ ℓ u v = 1) → False := by
  classical
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
  intro hU hin
  have hcov : ∀ v ∈ U, ∃ y, v ∈ X y := by
    intro v hv
    obtain ⟨u, _, _, ⟨y, _, hvy⟩, _⟩ := hin v hv
    exact ⟨y, hvy⟩
  obtain ⟨v, hv, z, hvz, hsimp⟩ := simplicial ht X hiii U hU hcov
  obtain ⟨u0, hu0, hu0v, ⟨y0, hu0y, hvy0⟩, hl0⟩ := hin v hv
  have hu0z : u0 ∈ X z := hsimp u0 hu0 y0 hu0y hvy0
  apply ih (U.erase v) (Finset.erase_ssubset hv) ⟨u0, Finset.mem_erase.2 ⟨hu0v, hu0⟩⟩
  intro w hw
  obtain ⟨hwv, hwU⟩ := Finset.mem_erase.1 hw
  obtain ⟨x, hx, hxw, ⟨y, hxy, hwy⟩, hlx⟩ := hin w hwU
  by_cases hxv : x = v
  · subst hxv
    have hwz : w ∈ X z := hsimp w hwU y hwy hxy
    have hu0w : u0 ≠ w := by
      intro h
      subst h
      have := h1 z u0 hu0z x hvz hu0v
      omega
    refine ⟨u0, Finset.mem_erase.2 ⟨hu0v, hu0⟩, hu0w, ⟨z, hu0z, hwz⟩, ?_⟩
    have hs := h1 z u0 hu0z w hwz hu0w
    have ht3 := h2 z u0 hu0z x hvz w hwz hu0v hxw hu0w
    omega
  · exact ⟨x, Finset.mem_erase.2 ⟨hxv, hx⟩, hxw, ⟨y, hxy, hwy⟩, hlx⟩

end TAChordal

namespace TraceAdopt.LPReform

theorem ta_ltm_mem (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (v : Fin I.n ⊕ Fin I.m) :
    v ∈ ltmStep I S ↔ v ∈ S ∨ (v ∉ S ∧
      match v with
      | Sum.inl i => I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i
      | Sum.inr j => I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card) := by
  classical
  unfold ltmStep
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1, ?_⟩
      cases v with
      | inl i => simpa using h2
      | inr j => simpa using h2

theorem ta_ltm_inl (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (i : Fin I.n) :
    Sum.inl i ∈ ltmStep I S ↔ Sum.inl i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
          (fun j => Sum.inr j ∈ S ∧ i ∈ I.e j), I.r j i := by
  rw [ta_ltm_mem]
  tauto

theorem ta_ltm_inr (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) (j : Fin I.m) :
    Sum.inr j ∈ ltmStep I S ↔ Sum.inr j ∈ S ∨ I.θ j - 1 ≤
          (Finset.univ.filter (fun i => Sum.inl i ∈ S ∧ i ∈ I.e j)).card := by
  rw [ta_ltm_mem]
  tauto

theorem ta_step_mem (I : Instance) (S : Finset (Fin I.n)) (i : Fin I.n) :
    i ∈ step I S ↔ i ∈ S ∨ I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (S ∩ I.e j).card), I.r j i := by
  unfold step
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem ta_step_mono (I : Instance) {S U : Finset (Fin I.n)} (h : S ⊆ U) :
    step I S ⊆ step I U := by
  intro i hi
  rw [ta_step_mem] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl (h hi)
  · right
    refine le_trans hi (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _))
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.1, le_trans hj.2 (Finset.card_le_card (Finset.inter_subset_inter_right h))⟩

theorem ta_step_ext (I : Instance) (S : Finset (Fin I.n)) : S ⊆ step I S := by
  intro i hi; rw [ta_step_mem]; exact Or.inl hi

theorem ta_ltm_ext (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) : S ⊆ ltmStep I S := by
  intro v hv; rw [ta_ltm_mem]; exact Or.inl hv

theorem ta_iter_step_succ_sub (I : Instance) (S : Finset (Fin I.n)) (t : ℕ) :
    (step I)^[t] S ⊆ (step I)^[t+1] S := by
  rw [Function.iterate_succ_apply']
  exact ta_step_ext I _

theorem ta_iter_ltm_mono (I : Instance) (S : Finset (Fin I.n ⊕ Fin I.m)) {a b : ℕ}
    (h : a ≤ b) : (ltmStep I)^[a] S ⊆ (ltmStep I)^[b] S := by
  induction b with
  | zero => simp at h; subst h; exact le_rfl
  | succ b ih =>
    rcases Nat.of_le_succ h with h | h
    · rw [Function.iterate_succ_apply']
      exact (ih h).trans (ta_ltm_ext I _)
    · rw [h]


theorem ta_iter_step_mono (I : Instance) (S : Finset (Fin I.n)) {a b : ℕ}
    (h : a ≤ b) : (step I)^[a] S ⊆ (step I)^[b] S := by
  induction b with
  | zero => simp at h; subst h; exact le_rfl
  | succ b ih =>
    rcases Nat.of_le_succ h with h | h
    · exact (ih h).trans (ta_iter_step_succ_sub I S b)
    · rw [h]

section P5
variable (I : Instance)

/-- Two-step relation through a supplier. -/
def taR (lFS : Fin I.n → Fin I.m → ℕ) (lSF : Fin I.m → Fin I.n → ℕ) (a b : Fin I.n) : Prop :=
  ∃ j, lFS a j = 1 ∧ lSF j b = 1

theorem taR_trans {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) {a b c : Fin I.n}
    (hab : taR I lFS lSF a b) (hbc : taR I lFS lSF b c) : taR I lFS lSF a c := by
  obtain ⟨j, h1, h2⟩ := hab
  obtain ⟨k, h3, h4⟩ := hbc
  refine ⟨k, ?_, h4⟩
  have hc := h.2.2.2.2.1 a k
  have hd := h.2.2.2.2.2 a b j k
  have hb := h.2.1 a k
  omega

theorem taR_irrefl {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) (a : Fin I.n) : ¬ taR I lFS lSF a a := by
  rintro ⟨j, h1, h2⟩
  have hc := h.2.2.2.2.1 a j
  omega

open Classical in
theorem taR_rank {s : Fin I.n → ℕ} {lFS : Fin I.n → Fin I.m → ℕ} {lSF : Fin I.m → Fin I.n → ℕ}
    (h : BiLP4Feasible I s lFS lSF) {a b : Fin I.n} (hab : taR I lFS lSF a b) :
    (Finset.univ.filter (fun x => taR I lFS lSF x a)).card <
      (Finset.univ.filter (fun x => taR I lFS lSF x b)).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, by simp [hab], by simp [taR_irrefl I h a]⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact taR_trans I h hx hab

/-- Feasibility of (4) forces full activation. -/
theorem ta_feas_imp (s : Fin I.n → ℕ) (lFS : Fin I.n → Fin I.m → ℕ)
    (lSF : Fin I.m → Fin I.n → ℕ) (h : BiLP4Feasible I s lFS lSF) :
    FullyActivates I (Finset.univ.filter (fun i => s i = 1)) := by
  classical
  set S := Finset.univ.filter (fun i => s i = 1) with hS
  have hmono : Monotone (fun t => (step I)^[t] S) :=
    fun a b hab => ta_iter_step_mono I S hab
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (α := Finset (Fin I.n)) ⟨fun t => (step I)^[t] S, hmono⟩
  set A := (step I)^[N] S with hA
  have hfix : step I A = A := by
    have := hN (N + 1) (by omega)
    simp only [OrderHom.coe_mk] at this
    show step I ((step I)^[N] S) = (step I)^[N] S
    rw [← Function.iterate_succ_apply' (step I) N S]; exact this.symm
  refine ⟨N, ?_⟩
  rw [← hA]
  apply Finset.eq_univ_of_forall
  suffices H : ∀ k, ∀ i, (Finset.univ.filter (fun x => taR I lFS lSF x i)).card = k → i ∈ A by
    intro i; exact H _ i rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i hk
  by_contra hiA
  have hiS : s i = 0 := by
    have hle := h.1 i
    have : i ∉ S := fun hi => hiA (ta_iter_step_mono I S (Nat.zero_le N) hi)
    simp [hS] at this
    omega
  have h4a := h.2.2.1 i
  rw [hiS, Nat.mul_zero, Nat.add_zero] at h4a
  have hnot : ¬ (I.c i ≤ ∑ j ∈ Finset.univ.filter
      (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (A ∩ I.e j).card), I.r j i) := by
    intro hc
    apply hiA
    rw [← hfix, ta_step_mem]
    exact Or.inr hc
  -- find a supplier j pointing to i that is not activated by A
  have hj : ∃ j, i ∈ I.e j ∧ lSF j i = 1 ∧ (A ∩ I.e j).card < I.θ j - 1 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    refine le_trans h4a ?_
    rw [← Finset.filter_filter, Finset.sum_filter (p := fun j => I.θ j - 1 ≤ (A ∩ I.e j).card)]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hl := (h.2.1 i j).2
    split_ifs with hc
    · calc I.r j i * lSF j i ≤ I.r j i * 1 := Nat.mul_le_mul_left _ hl
        _ = I.r j i := by ring
    · have : lSF j i ≠ 1 := fun h1 => hc (hcon j hj h1)
      have : lSF j i = 0 := by omega
      simp [this]
  obtain ⟨j, hij, hl, hcard⟩ := hj
  have h4b := h.2.2.2.1 j
  have hi' : ∃ i', i' ∈ I.e j ∧ lFS i' j = 1 ∧ i' ∉ A := by
    by_contra hcon
    push Not at hcon
    have : (∑ x ∈ Finset.univ.filter (fun x => x ∈ I.e j), lFS x j) ≤ (A ∩ I.e j).card := by
      have hAe : A ∩ I.e j = Finset.univ.filter (fun x => x ∈ I.e j ∧ x ∈ A) := by
        ext x; simp; tauto
      rw [hAe, Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x _
      have hl := (h.2.1 x j).1
      by_cases hx : x ∈ I.e j
      · by_cases hxA : x ∈ A
        · simp [hx, hxA]; exact hl
        · have : lFS x j ≠ 1 := fun h1 => hxA (hcon x hx h1)
          have : lFS x j = 0 := by omega
          simp [hx, hxA, this]
      · simp [hx]
    omega
  obtain ⟨i', _, hl', hi'A⟩ := hi'
  have hR : taR I lFS lSF i' i := ⟨j, hl', hl⟩
  exact hi'A (ih _ (hk ▸ taR_rank I h hR) i' rfl)

/-- A fully activating seed set yields a feasible solution of (4). -/
theorem ta_imp_feas (S : Finset (Fin I.n)) (hS : FullyActivates I S) (hθ : ∀ j, I.θ j ≤ (I.e j).card) :
    ∃ lFS lSF, BiLP4Feasible I (fun i => if i ∈ S then 1 else 0) lFS lSF := by
  classical
  obtain ⟨T, hT⟩ := hS
  have hex : ∀ i, ∃ t, i ∈ (step I)^[t] S := fun i => ⟨T, by rw [hT]; exact Finset.mem_univ i⟩
  have hexj : ∀ j, ∃ t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card := by
    intro j; refine ⟨T, ?_⟩
    rw [hT, Finset.univ_inter]; have := hθ j; omega
  let τ : Fin I.n → ℕ := fun i => Nat.find (hex i)
  let σ : Fin I.m → ℕ := fun j => Nat.find (hexj j)
  have hτ : ∀ i t, i ∈ (step I)^[t] S ↔ τ i ≤ t := by
    intro i t
    constructor
    · intro h; exact Nat.find_min' (hex i) h
    · intro h; exact ta_iter_step_mono I S h (Nat.find_spec (hex i))
  have hσ : ∀ j t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card ↔ σ j ≤ t := by
    intro j t
    constructor
    · intro h; exact Nat.find_min' (hexj j) h
    · intro h
      exact le_trans (Nat.find_spec (hexj j)) (Finset.card_le_card
        (Finset.inter_subset_inter_right (ta_iter_step_mono I S h)))
  refine ⟨fun i j => if τ i ≤ σ j then 1 else 0, fun j i => if σ j < τ i then 1 else 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only; split_ifs <;> omega
  · intro i j; dsimp only; constructor <;> split_ifs <;> omega
  · intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, if_false, Nat.mul_zero, Nat.add_zero]
      have hτpos : τ i ≠ 0 := by
        intro h0
        have := (hτ i 0).2 (by omega)
        simp at this
        exact hi this
      obtain ⟨t, ht⟩ : ∃ t, τ i = t + 1 := ⟨τ i - 1, by omega⟩
      have hin : i ∈ (step I)^[t+1] S := (hτ i _).2 (le_of_eq ht)
      have hnin : i ∉ (step I)^[t] S := fun h => by have := (hτ i t).1 h; omega
      rw [Function.iterate_succ_apply', ta_step_mem] at hin
      rcases hin with hin | hin
      · exact absurd hin hnin
      refine le_trans hin ?_
      rw [← Finset.filter_filter, Finset.sum_filter (p := fun j => I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card)]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h1 h2
      · simp
      · exfalso; have := (hσ j t).1 h1; omega
      · exact Nat.zero_le _
      · exact Nat.zero_le _
  · intro j
    have hs := (hσ j (σ j)).2 le_rfl
    refine le_trans hs ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have : (step I)^[σ j] S ∩ I.e j = Finset.univ.filter (fun i => i ∈ I.e j ∧ i ∈ (step I)^[σ j] S) := by
      ext x; simp; tauto
    rw [this, ← Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    have hτx := hτ x (σ j)
    dsimp only
    split_ifs <;> simp_all
  · intro i j; simp only; split_ifs <;> omega
  · intro i₁ i₂ j₁ j₂; simp only; split_ifs <;> omega

end P5


section P7

/-- Feasibility of (5) forces full activation, via the chordal acyclicity lemma. -/
theorem ta_feas5_imp (I : Instance) {T : Type} [Fintype T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (hX : RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) t X')
    (s : Fin I.n → ℕ) (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
    (h : BiLP5Feasible I X' s ℓ) :
    FullyActivates I (Finset.univ.filter (fun i => s i = 1)) := by
  classical
  obtain ⟨htree, _, hedge, hpath⟩ := hX
  have hbag : ∀ i j, i ∈ I.e j → ∃ z, Sum.inr j ∈ X' z ∧ Sum.inl i ∈ X' z := by
    intro i j hij
    exact hedge (Sum.inr j) (Sum.inl i) (by simpa [auxGraph] using hij)
  have hle1 : ∀ i j, i ∈ I.e j → ℓ (Sum.inr j) (Sum.inl i) ≤ 1 ∧ ℓ (Sum.inl i) (Sum.inr j) ≤ 1 := by
    intro i j hij
    obtain ⟨z, hz1, hz2⟩ := hbag i j hij
    exact ⟨h.2.1 z _ hz1 _ hz2, h.2.1 z _ hz2 _ hz1⟩
  set S := Finset.univ.filter (fun i => s i = 1) with hS
  have hmono : Monotone (fun t => (step I)^[t] S) :=
    fun a b hab => ta_iter_step_mono I S hab
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (α := Finset (Fin I.n)) ⟨fun t => (step I)^[t] S, hmono⟩
  set A := (step I)^[N] S with hA
  have hfix : step I A = A := by
    have := hN (N + 1) (by omega)
    simp only [OrderHom.coe_mk] at this
    show step I ((step I)^[N] S) = (step I)^[N] S
    rw [← Function.iterate_succ_apply' (step I) N S]; exact this.symm
  refine ⟨N, ?_⟩
  rw [← hA]
  apply Finset.eq_univ_of_forall
  intro i0
  by_contra hi0
  let stuck : Fin I.n ⊕ Fin I.m → Prop :=
    Sum.elim (fun i => i ∉ A) (fun j => (A ∩ I.e j).card < I.θ j - 1)
  let U := Finset.univ.filter stuck
  have hmemU : ∀ v, v ∈ U ↔ stuck v := by intro v; simp [U]
  apply TAChordal.noBad htree X' hpath ℓ h.2.2.2.2.1 h.2.2.2.2.2 U ⟨Sum.inl i0, (hmemU _).2 hi0⟩
  intro v hv
  rw [hmemU] at hv
  cases v with
  | inl i =>
    have hiA : i ∉ A := hv
    have hiS : s i = 0 := by
      have hle := h.1 i
      have : i ∉ S := fun hi => hiA (ta_iter_step_mono I S (Nat.zero_le N) hi)
      simp [hS] at this
      omega
    have h4a := h.2.2.1 i
    rw [hiS, Nat.mul_zero, Nat.add_zero] at h4a
    have hnot : ¬ (I.c i ≤ ∑ j ∈ Finset.univ.filter
        (fun j => i ∈ I.e j ∧ I.θ j - 1 ≤ (A ∩ I.e j).card), I.r j i) := by
      intro hc
      apply hiA
      rw [← hfix, ta_step_mem]
      exact Or.inr hc
    have hj : ∃ j, i ∈ I.e j ∧ ℓ (Sum.inr j) (Sum.inl i) = 1 ∧ (A ∩ I.e j).card < I.θ j - 1 := by
      by_contra hcon
      push Not at hcon
      apply hnot
      refine le_trans h4a ?_
      rw [← Finset.filter_filter, Finset.sum_filter (p := fun j => I.θ j - 1 ≤ (A ∩ I.e j).card)]
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hl := (hle1 i j hj).1
      split_ifs with hc
      · calc I.r j i * ℓ (Sum.inr j) (Sum.inl i) ≤ I.r j i * 1 := Nat.mul_le_mul_left _ hl
          _ = I.r j i := by ring
      · have : ℓ (Sum.inr j) (Sum.inl i) ≠ 1 := fun h1 => hc (hcon j hj h1)
        have : ℓ (Sum.inr j) (Sum.inl i) = 0 := by omega
        simp [this]
    obtain ⟨j, hij, hl, hcard⟩ := hj
    obtain ⟨z, hz1, hz2⟩ := hbag i j hij
    exact ⟨Sum.inr j, (hmemU _).2 hcard, by simp, ⟨z, hz1, hz2⟩, hl⟩
  | inr j =>
    have hcard : (A ∩ I.e j).card < I.θ j - 1 := hv
    have h4b := h.2.2.2.1 j
    have hi' : ∃ i', i' ∈ I.e j ∧ ℓ (Sum.inl i') (Sum.inr j) = 1 ∧ i' ∉ A := by
      by_contra hcon
      push Not at hcon
      have : (∑ x ∈ Finset.univ.filter (fun x => x ∈ I.e j), ℓ (Sum.inl x) (Sum.inr j)) ≤
          (A ∩ I.e j).card := by
        have hAe : A ∩ I.e j = Finset.univ.filter (fun x => x ∈ I.e j ∧ x ∈ A) := by
          ext x; simp; tauto
        rw [hAe, Finset.card_filter, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : x ∈ I.e j
        · have hl := (hle1 x j hx).2
          by_cases hxA : x ∈ A
          · simp [hx, hxA]; exact hl
          · have : ℓ (Sum.inl x) (Sum.inr j) ≠ 1 := fun h1 => hxA (hcon x hx h1)
            have : ℓ (Sum.inl x) (Sum.inr j) = 0 := by omega
            simp [hx, hxA, this]
        · simp [hx]
      omega
    obtain ⟨i', hi'e, hl', hi'A⟩ := hi'
    obtain ⟨z, hz1, hz2⟩ := hbag i' j hi'e
    exact ⟨Sum.inl i', (hmemU _).2 hi'A, by simp, ⟨z, hz2, hz1⟩, hl'⟩

/-- A fully activating seed set yields a feasible solution of (5) (for any bags). -/
theorem ta_imp_feas5 (I : Instance) {T : Type} (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (S : Finset (Fin I.n)) (hS : FullyActivates I S)
    (hθ : ∀ j, I.θ j ≤ (I.e j).card) :
    ∃ ℓ, BiLP5Feasible I X' (fun i => if i ∈ S then 1 else 0) ℓ := by
  classical
  obtain ⟨T0, hT⟩ := hS
  have hex : ∀ i, ∃ t, i ∈ (step I)^[t] S := fun i => ⟨T0, by rw [hT]; exact Finset.mem_univ i⟩
  have hexj : ∀ j, ∃ t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card := by
    intro j; refine ⟨T0, ?_⟩
    rw [hT, Finset.univ_inter]; have := hθ j; omega
  let τ : Fin I.n → ℕ := fun i => Nat.find (hex i)
  let σ : Fin I.m → ℕ := fun j => Nat.find (hexj j)
  have hτ : ∀ i t, i ∈ (step I)^[t] S ↔ τ i ≤ t := by
    intro i t
    constructor
    · intro h; exact Nat.find_min' (hex i) h
    · intro h; exact ta_iter_step_mono I S h (Nat.find_spec (hex i))
  have hσ : ∀ j t, I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card ↔ σ j ≤ t := by
    intro j t
    constructor
    · intro h; exact Nat.find_min' (hexj j) h
    · intro h
      exact le_trans (Nat.find_spec (hexj j)) (Finset.card_le_card
        (Finset.inter_subset_inter_right (ta_iter_step_mono I S h)))
  let tm : Fin I.n ⊕ Fin I.m → ℕ := Sum.elim (fun i => 2 * τ i) (fun j => 2 * σ j + 1)
  let ix : Fin I.n ⊕ Fin I.m → ℕ := Sum.elim (fun i => i.val) (fun j => I.n + j.val)
  have hinj : ∀ u v, tm u = tm v → ix u = ix v → u = v := by
    intro u v h1 h2
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [ix] at h2; rw [Fin.ext h2]
      | inr k => simp [ix] at h2; omega
    | inr j =>
      cases v with
      | inl k => simp [ix] at h2; omega
      | inr k => simp [ix] at h2; rw [Fin.ext h2]
  let ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ := fun u v =>
    if tm u < tm v ∨ (tm u = tm v ∧ ix u < ix v) then 1 else 0
  refine ⟨ℓ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; dsimp only; split_ifs <;> omega
  · intro z u _ v _; dsimp only [ℓ]; split_ifs <;> omega
  · intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, if_false, Nat.mul_zero, Nat.add_zero]
      have hτpos : τ i ≠ 0 := by
        intro h0
        have := (hτ i 0).2 (by omega)
        simp at this
        exact hi this
      obtain ⟨t, ht⟩ : ∃ t, τ i = t + 1 := ⟨τ i - 1, by omega⟩
      have hin : i ∈ (step I)^[t+1] S := (hτ i _).2 (le_of_eq ht)
      have hnin : i ∉ (step I)^[t] S := fun h => by have := (hτ i t).1 h; omega
      rw [Function.iterate_succ_apply', ta_step_mem] at hin
      rcases hin with hin | hin
      · exact absurd hin hnin
      refine le_trans hin ?_
      rw [← Finset.filter_filter,
        Finset.sum_filter (p := fun j => I.θ j - 1 ≤ ((step I)^[t] S ∩ I.e j).card)]
      apply Finset.sum_le_sum
      intro j _
      have hσj := hσ j t
      dsimp only [ℓ, tm, Sum.elim_inl, Sum.elim_inr]
      split_ifs <;> simp_all <;> omega
  · intro j
    have hs := (hσ j (σ j)).2 le_rfl
    refine le_trans hs ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have : (step I)^[σ j] S ∩ I.e j =
        Finset.univ.filter (fun i => i ∈ I.e j ∧ i ∈ (step I)^[σ j] S) := by
      ext x; simp; tauto
    rw [this, ← Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro x _
    have hτx := hτ x (σ j)
    dsimp only [ℓ, tm, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp_all <;> omega
  · intro z u _ v _ huv
    have := hinj u v
    dsimp only [ℓ]
    split_ifs <;> first | omega | (exfalso; apply huv; apply this <;> omega)
  · intro z u _ v _ x _ _ _ _
    dsimp only [ℓ]
    split_ifs <;> omega

end P7

theorem ta_prop7 (I : Instance) (hI : I.Standing) {T : Type} [Fintype T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (hX : RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) t X') :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ, BiLP5Feasible I X' s ℓ) ↔ ∃ lFS lSF, BiLP4Feasible I s lFS lSF) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
      BiLP5Feasible I X' s ℓ →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
        BiLP5Feasible I X' s' ℓ' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) := by
  classical
  have hθ : ∀ j, I.θ j ≤ (I.e j).card := fun j => (hI.2.1 j).2
  have hsum : ∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ), (∀ i, s i ≤ 1) →
      (∑ i, w i * (s i : ℝ)) = ∑ i ∈ Finset.univ.filter (fun i => s i = 1), w i := by
    intro w s hs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    have := hs i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [h]
  have hind : ∀ s : Fin I.n → ℕ, (∀ i, s i ≤ 1) →
      s = fun i => if i ∈ Finset.univ.filter (fun i => s i = 1) then 1 else 0 := by
    intro s hs
    funext i
    have := hs i
    by_cases hi : s i = 1 <;> simp [hi] <;> omega
  refine ⟨?_, ?_⟩
  · intro s
    constructor
    · rintro ⟨ℓ, h⟩
      have hfa := ta_feas5_imp I t X' hX s ℓ h
      obtain ⟨lFS, lSF, h4⟩ := ta_imp_feas I _ hfa hθ
      refine ⟨lFS, lSF, ?_⟩
      rw [hind s h.1]; exact h4
    · rintro ⟨lFS, lSF, h⟩
      have hfa := ta_feas_imp I s lFS lSF h
      obtain ⟨ℓ, h5⟩ := ta_imp_feas5 I X' _ hfa hθ
      refine ⟨ℓ, ?_⟩
      rw [hind s h.1]; exact h5
  · intro w s ℓ h hopt
    have hfa := ta_feas5_imp I t X' hX s ℓ h
    refine ⟨hfa, ?_⟩
    rw [hsum w s h.1]
    apply le_antisymm
    · unfold OPT
      apply Finset.le_inf'
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨ℓ', h'⟩ := ta_imp_feas5 I X' S hS hθ
      have := hopt _ ℓ' h'
      rw [hsum w s h.1, hsum w _ h'.1] at this
      refine le_trans this (le_of_eq ?_)
      congr 1
      ext i; simp
    · unfold OPT
      apply Finset.inf'_le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfa

end TraceAdopt.LPReform

open TraceAdopt.LPReform in
theorem solution (I : Instance) (hI : I.Standing) {T : Type} [Fintype T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m))
    (hX : RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) t X') :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ, BiLP5Feasible I X' s ℓ) ↔ ∃ lFS lSF, BiLP4Feasible I s lFS lSF) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
      BiLP5Feasible I X' s ℓ →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ),
        BiLP5Feasible I X' s' ℓ' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) :=
  ta_prop7 I hI t X' hX
