-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:02:21.641071+00:00
-- url     : https://prove2.me/submissions/a13008b8-328d-4ba3-a07f-943ff49b10dc

import Definitions.Def_TraceAdopt_LPReform_BiLP4
import Definitions.Def_TraceAdopt_LPReform_BiLP5
import Definitions.Def_TraceAdopt_LPReform_BiLP10

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


namespace TARooted

open SimpleGraph

section
variable {T : Type} (rt : T) (par : T → T) (hrt : par rt = rt)
  (hreach : ∀ z, ∃ k, par^[k] z = rt)

theorem iter_rt (k : ℕ) (hrt : par rt = rt) : par^[k] rt = rt := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hrt]

include hrt hreach in
theorem cyc (x : T) (d : ℕ) (h : par^[d + 1] x = x) : x = rt := by
  obtain ⟨K, hK⟩ := hreach x
  have hmul : ∀ N, par^[(d + 1) * N] x = x := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]
  have h1 := hmul K
  have hle : K ≤ (d + 1) * K := Nat.le_mul_of_pos_left K (by omega)
  have : par^[(d + 1) * K] x = par^[(d + 1) * K - K] (par^[K] x) := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
  rw [this, hK, iter_rt rt par _ hrt] at h1
  exact h1.symm

end

section
variable {T : Type} [Fintype T] [DecidableEq T] (t : SimpleGraph T) (rt : T) (par : T → T)
  (hrt : par rt = rt) (hadj : ∀ z, z ≠ rt → t.Adj z (par z)) (hreach : ∀ z, ∃ k, par^[k] z = rt)
  (htree : t.IsTree)

include hrt hadj hreach htree in
/-- Every edge of the tree is a parent edge. -/
theorem parent_edge {x y : T} (h : t.Adj x y) :
    (x ≠ rt ∧ par x = y) ∨ (y ≠ rt ∧ par y = x) := by
  classical
  have hcard := (isTree_iff_connected_and_card.1 htree).2
  let P : Set (Sym2 T) := (fun z => s(z, par z)) '' {z | z ≠ rt}
  have hPsub : P ⊆ t.edgeSet := by
    rintro e ⟨z, hz, rfl⟩
    exact hadj z hz
  have hinj : Set.InjOn (fun z => s(z, par z)) {z | z ≠ rt} := by
    intro a ha b hb hab
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hab
    rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      apply ha
      apply cyc rt par hrt hreach a 1
      rw [Function.iterate_succ_apply', Function.iterate_one, h2, ← h1]
  have hPcard : P.ncard = Nat.card T - 1 := by
    rw [Set.ncard_image_of_injOn hinj]
    have : {z : T | z ≠ rt} = (({rt} : Set T)ᶜ) := by ext; simp
    rw [this, Set.ncard_compl, Set.ncard_singleton]
  have hE : t.edgeSet.ncard = Nat.card T - 1 := by
    rw [← Nat.card_coe_set_eq]; omega
  have hPeq : P = t.edgeSet :=
    Set.eq_of_subset_of_ncard_le hPsub (by rw [hE, hPcard]) (Set.toFinite _)
  have hxy : s(x, y) ∈ P := by rw [hPeq]; exact h
  obtain ⟨z, hz, hze⟩ := hxy
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hze
  rcases hze with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨hz, rfl⟩
  · exact Or.inr ⟨hz, rfl⟩

/-- Descendants. -/
def Desc (z x : T) : Prop := ∃ k, par^[k] x = z

include hrt hadj hreach htree in
/-- A walk leaving the descendants of `z` passes through the parent of `z`. -/
theorem exit_walk (z : T) : ∀ {a b : T} (w : t.Walk a b), Desc par z a → ¬ Desc par z b →
    z ≠ rt ∧ par z ∈ w.support := by
  intro a b w
  induction w with
  | nil => intro h1 h2; exact absurd h1 h2
  | @cons x y b' hxy w ih =>
    intro hx hb
    by_cases hy : Desc par z y
    · obtain ⟨h1, h2⟩ := ih hy hb
      exact ⟨h1, by simp [h2]⟩
    · rcases parent_edge t rt par hrt hadj hreach htree hxy with ⟨hxr, hpx⟩ | ⟨hyr, hpy⟩
      · -- `y` is the parent of `x`
        obtain ⟨k, hk⟩ := hx
        cases k with
        | zero =>
          simp at hk
          subst hk
          refine ⟨hxr, ?_⟩
          simp [hpx]
        | succ k =>
          exfalso; apply hy
          refine ⟨k, ?_⟩
          rw [← hpx, ← Function.iterate_succ_apply]
          exact hk
      · exfalso; apply hy
        obtain ⟨k, hk⟩ := hx
        refine ⟨k + 1, ?_⟩
        rw [Function.iterate_succ_apply, hpy]
        exact hk

variable (M : T → Prop) [DecidablePred M]

/-- `z` is the root of the subtree of nodes satisfying `M`. -/
def IsRootM (z : T) : Prop := M z ∧ (z = rt ∨ ¬ M (par z))

include hrt hadj hreach htree in
theorem root_unique
    (hM : ∀ a b, M a → M b → ∃ w : t.Walk a b, ∀ c ∈ w.support, M c)
    {z0 z1 : T} (h0 : IsRootM rt par M z0) (h1 : IsRootM rt par M z1) : z0 = z1 := by
  have key : ∀ {a b : T}, IsRootM rt par M a → IsRootM rt par M b → Desc par a b := by
    intro a b ha hb
    by_contra hd
    obtain ⟨w, hw⟩ := hM a b ha.1 hb.1
    obtain ⟨har, hpa⟩ := exit_walk t rt par hrt hadj hreach htree a w ⟨0, rfl⟩ hd
    rcases ha.2 with h | h
    · exact har h
    · exact h (hw _ hpa)
  obtain ⟨k, hk⟩ := key h0 h1
  obtain ⟨k', hk'⟩ := key h1 h0
  cases k with
  | zero => exact hk.symm
  | succ k =>
    have : par^[k + k' + 1] z0 = z0 := by
      have e : k + k' + 1 = (k + 1) + k' := by ring
      rw [e, Function.iterate_add_apply, hk', hk]
    have hz0 := cyc rt par hrt hreach z0 (k + k') this
    rw [hz0] at hk' ⊢
    rw [iter_rt _ _ _ hrt] at hk'
    exact hk'

/-- Descendants of `z` inside the `M`-subtree. -/
def SubM (z x : T) : Prop := ∃ k, par^[k] x = z ∧ ∀ k' ≤ k, M (par^[k'] x)

include hrt hreach in
theorem exists_root (x : T) (hx : M x) : ∃ z0, IsRootM rt par M z0 ∧ SubM par M z0 x := by
  classical
  have hex : ∃ k, par^[k] x = rt ∨ ¬ M (par^[k + 1] x) := by
    obtain ⟨K, hK⟩ := hreach x
    exact ⟨K, Or.inl hK⟩
  let k0 := Nat.find hex
  have hall : ∀ k' ≤ k0, M (par^[k'] x) := by
    intro k' hk'
    induction k' with
    | zero => exact hx
    | succ k' ih =>
      have hlt : k' < k0 := by omega
      have := Nat.find_min hex hlt
      push Not at this
      exact this.2
  refine ⟨par^[k0] x, ⟨hall k0 le_rfl, ?_⟩, ⟨k0, rfl, hall⟩⟩
  have := Nat.find_spec hex
  rcases this with h | h
  · exact Or.inl h
  · right
    rw [← Function.iterate_succ_apply' par k0 x]
    exact h

/-- Children of `z` (as in the platform definition). -/
def ch (z : T) : Finset T := Finset.univ.filter (fun z' => z' ≠ rt ∧ par z' = z)

include hrt hreach in
theorem sub_decomp (z : T) (hz : M z) (x : T) :
    SubM par M z x ↔ x = z ∨ ∃ c ∈ (ch rt par z).filter M, SubM par M c x := by
  classical
  constructor
  · rintro hx
    by_cases hxz : x = z
    · exact Or.inl hxz
    right
    let k := Nat.find hx
    have hk : par^[k] x = z ∧ ∀ k' ≤ k, M (par^[k'] x) := Nat.find_spec hx
    have hk0 : k ≠ 0 := by
      intro h0
      have := hk.1
      rw [h0] at this
      exact hxz this
    obtain ⟨k1, hk1⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
    have hc : par (par^[k1] x) = z := by
      have h' : par^[k1 + 1] x = z := hk1 ▸ hk.1
      rwa [Function.iterate_succ_apply'] at h'
    have hcne : par^[k1] x ≠ z := by
      intro h
      have := Nat.find_min' hx ⟨h, fun k' hk' => hk.2 k' (by omega)⟩
      omega
    have hcrt : par^[k1] x ≠ rt := by
      intro h
      apply hcne
      rw [← hc, h, hrt]
    refine ⟨par^[k1] x, ?_, ⟨k1, rfl, fun k' hk' => hk.2 k' (by omega)⟩⟩
    simp only [Finset.mem_filter, ch, Finset.mem_univ, true_and]
    exact ⟨⟨hcrt, hc⟩, hk.2 k1 (by omega)⟩
  · rintro (rfl | ⟨c, hc, ⟨k, hk, hkM⟩⟩)
    · exact ⟨0, rfl, fun k' hk' => by
        have : k' = 0 := by omega
        subst this; exact hz⟩
    · simp only [Finset.mem_filter, ch, Finset.mem_univ, true_and] at hc
      refine ⟨k + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hk, hc.1.2]
      · intro k' hk'
        rcases Nat.lt_or_ge k' (k + 1) with h | h
        · exact hkM k' (by omega)
        · have : k' = k + 1 := by omega
          subst this
          rw [Function.iterate_succ_apply', hk, hc.1.2]
          exact hz

include hrt hreach in
theorem sub_not_self (z c : T) (hc : c ∈ ch rt par z) : ¬ SubM par M c z := by
  rintro ⟨k, hk, _⟩
  simp only [ch, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  apply hc.1
  apply cyc rt par hrt hreach c k
  rw [Function.iterate_succ_apply, hc.2, hk]

include hrt hreach in
theorem sub_disjoint (z c1 c2 : T) (h1 : c1 ∈ ch rt par z) (h2 : c2 ∈ ch rt par z) (hne : c1 ≠ c2)
    (x : T) (hx1 : SubM par M c1 x) (hx2 : SubM par M c2 x) : False := by
  simp only [ch, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  obtain ⟨k1, hk1, _⟩ := hx1
  obtain ⟨k2, hk2, _⟩ := hx2
  have gen : ∀ (a b : T) (ka kb : ℕ), a ≠ rt ∧ par a = z → b ≠ rt ∧ par b = z → a ≠ b →
      par^[ka] x = a → par^[kb] x = b → ka ≤ kb → False := by
    intro a b ka kb ha hb hab hka hkb hle
    obtain ⟨d, rfl⟩ : ∃ d, kb = ka + d := ⟨kb - ka, by omega⟩
    rw [Nat.add_comm, Function.iterate_add_apply, hka] at hkb
    cases d with
    | zero => exact hab (by simpa using hkb)
    | succ d =>
      rw [Function.iterate_succ_apply, ha.2] at hkb
      -- `par^[d] z = b` and `par b = z`
      have hcyc : par^[d + 1] z = z := by
        rw [Function.iterate_succ_apply', hkb, hb.2]
      have hzr := cyc rt par hrt hreach z d hcyc
      subst hzr
      rw [iter_rt _ _ _ hrt] at hkb
      exact hb.1 hkb.symm
  rcases le_total k1 k2 with h | h
  · exact gen c1 c2 k1 k2 h1 h2 hne hk1 hk2 h
  · exact gen c2 c1 k2 k1 h2 h1 (Ne.symm hne) hk2 hk1 h

open Classical in
include hrt hreach in
theorem sum_decomp (z : T) (hz : M z) (f : T → ℕ) :
    (∑ x ∈ Finset.univ.filter (SubM par M z), f x) =
      f z + ∑ c ∈ (ch rt par z).filter M, ∑ x ∈ Finset.univ.filter (SubM par M c), f x := by
  classical
  have hset : Finset.univ.filter (SubM par M z) =
      insert z (((ch rt par z).filter M).biUnion (fun c => Finset.univ.filter (SubM par M c))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion]
    simpa using sub_decomp rt par hrt hreach M z hz x
  have hnot : z ∉ ((ch rt par z).filter M).biUnion (fun c => Finset.univ.filter (SubM par M c)) := by
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and]
    intro c hc hs
    exact sub_not_self rt par hrt hreach M z c hc.1 hs
  rw [hset, Finset.sum_insert hnot, Finset.sum_biUnion]
  intro c1 hc1 c2 hc2 hne
  simp only [Finset.coe_filter] at hc1 hc2
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
  exact sub_disjoint rt par hrt hreach M z c1 c2 hc1.1 hc2.1 hne x hx1 hx2

end


section Acc
variable {T : Type} [Fintype T] [DecidableEq T] (rt : T) (par : T → T)
  (hrt : par rt = rt) (hreach : ∀ z, ∃ k, par^[k] z = rt)
  (M : T → Prop) [DecidablePred M]

open Classical in
include hrt hreach in
/-- Accumulation along the `M`-subtree: the inequalities (10a), (10b) bound the partial sums. -/
theorem acc_upper (U UT A : T → ℕ)
    (ha : ∀ z, M z → U z ≤ A z)
    (hb : ∀ z, M z → ¬ IsRootM rt par M z → UT z ≤ U z + ∑ c ∈ (ch rt par z).filter M, UT c) :
    ∀ z, M z → U z + ∑ c ∈ (ch rt par z).filter M, UT c ≤
      ∑ x ∈ Finset.univ.filter (SubM par M z), A x := by
  suffices H : ∀ N, ∀ z, M z → (Finset.univ.filter (SubM par M z)).card ≤ N →
      U z + ∑ c ∈ (ch rt par z).filter M, UT c ≤ ∑ x ∈ Finset.univ.filter (SubM par M z), A x by
    intro z hz; exact H _ z hz le_rfl
  intro N
  induction N with
  | zero =>
    intro z hz hcard
    exfalso
    have : z ∈ Finset.univ.filter (SubM par M z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨0, rfl, fun k' hk' => by
        have : k' = 0 := by omega
        subst this; exact hz⟩
    have := Finset.card_pos.2 ⟨z, this⟩
    omega
  | succ N ih =>
    intro z hz hcard
    rw [sum_decomp rt par hrt hreach M z hz A]
    apply Nat.add_le_add (ha z hz)
    apply Finset.sum_le_sum
    intro c hc
    have hcM : M c := (Finset.mem_filter.1 hc).2
    have hcch := (Finset.mem_filter.1 hc).1
    have hcch' := hcch
    simp only [ch, Finset.mem_filter, Finset.mem_univ, true_and] at hcch'
    have hnr : ¬ IsRootM rt par M c := by
      rintro ⟨_, h | h⟩
      · exact hcch'.1 h
      · exact h (hcch'.2 ▸ hz)
    refine le_trans (hb c hcM hnr) ?_
    apply ih c hcM
    have hsub : Finset.univ.filter (SubM par M c) ⊂ Finset.univ.filter (SubM par M z) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨z, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨0, rfl, fun k' hk' => by
            have : k' = 0 := by omega
            subst this; exact hz⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact sub_not_self rt par hrt hreach M z c hcch
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact (sub_decomp rt par hrt hreach M z hz x).2 (Or.inr ⟨c, hc, hx⟩)
    have := Finset.card_lt_card hsub
    omega

theorem min_sum_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) :
    min (∑ x ∈ s, f x) c ≤ ∑ x ∈ s, min (f x) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : min (f a + ∑ x ∈ s, f x) c ≤ min (f a) c + min (∑ x ∈ s, f x) c := by
      rcases le_total (f a) c with h | h <;> rcases le_total (∑ x ∈ s, f x) c with h' | h' <;>
        simp only [min_def] <;> split_ifs <;> omega
    omega

open Classical in
include hrt hreach in
/-- The capped partial sums satisfy (10b). -/
theorem capped_b (A : T → ℕ) (c : ℕ) (z : T) (hz : M z) :
    min (∑ x ∈ Finset.univ.filter (SubM par M z), A x) c ≤
      min (A z) c + ∑ c' ∈ (ch rt par z).filter M,
        min (∑ x ∈ Finset.univ.filter (SubM par M c'), A x) c := by
  rw [sum_decomp rt par hrt hreach M z hz A]
  have h1 := min_sum_le ((ch rt par z).filter M)
    (fun c' => ∑ x ∈ Finset.univ.filter (SubM par M c'), A x) c
  have h2 : min (A z + ∑ c' ∈ (ch rt par z).filter M,
      ∑ x ∈ Finset.univ.filter (SubM par M c'), A x) c ≤
      min (A z) c + min (∑ c' ∈ (ch rt par z).filter M,
        ∑ x ∈ Finset.univ.filter (SubM par M c'), A x) c := by
    simp only [min_def]; split_ifs <;> omega
  omega

end Acc

end TARooted

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


section P8

/-- Binary digits of `x` (bits `0, …, K`). -/
def bitsOf (K x : ℕ) : Fin (K + 1) → ℕ := fun τ => x / 2 ^ τ.val % 2

theorem bitVal_bitsOf (K x : ℕ) (hx : x < 2 ^ (K + 1)) : bitVal (bitsOf K x) = x := by
  have key : ∀ k, ∑ τ ∈ Finset.range k, 2 ^ τ * (x / 2 ^ τ % 2) = x % 2 ^ k := by
    intro k
    induction k with
    | zero => simp [Nat.mod_one]
    | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]
  unfold bitVal bitsOf
  rw [Fin.sum_univ_eq_sum_range (fun τ => 2 ^ τ * (x / 2 ^ τ % 2)) (K + 1), key,
    Nat.mod_eq_of_lt hx]

theorem bitsOf_le (K x : ℕ) (τ : Fin (K + 1)) : bitsOf K x τ ≤ 1 := by
  unfold bitsOf; omega

variable (I : Instance) {T : Type} [Fintype T] [DecidableEq T]
  (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
  (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))

theorem part_sum_J (hJ : IsPartitionData I X' J Ip) (i : Fin I.n) (f : Fin I.m → ℕ) :
    (∑ z, ∑ j ∈ J i z, f j) = ∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j), f j := by
  classical
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨z, hz⟩; exact (hJ.1 i z j hz).1
    · intro h; exact hJ.2.2.1 i j h
  · intro z _ z' _ hne
    exact hJ.2.1 i z z' hne

theorem part_sum_Ip (hJ : IsPartitionData I X' J Ip) (j : Fin I.m) (f : Fin I.n → ℕ) :
    (∑ z, ∑ i ∈ Ip j z, f i) = ∑ i ∈ Finset.univ.filter (fun i => i ∈ I.e j), f i := by
  classical
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨z, hz⟩; exact (hJ.2.2.2.1 j z i hz).1
    · intro h; exact hJ.2.2.2.2.2 j i h
  · intro z _ z' _ hne
    exact hJ.2.2.2.2.1 j z z' hne

theorem walks_M (hX : IsRootedBinaryTD I t X' rt par) (w : Fin I.n ⊕ Fin I.m) :
    ∀ a b, w ∈ X' a → w ∈ X' b → ∃ p : t.Walk a b, ∀ c ∈ p.support, w ∈ X' c := by
  classical
  intro a b ha hb
  obtain ⟨⟨htree, _, _, hpath⟩, _⟩ := hX
  obtain ⟨p0⟩ := htree.connected.preconnected a b
  exact ⟨p0.bypass, fun c hc =>
    hpath a c b p0.bypass p0.bypass_isPath hc (Finset.mem_inter.2 ⟨ha, hb⟩)⟩

/-- (10) implies (5). -/
theorem ta_10_imp_5 (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip)
    (s : Fin I.n → ℕ) (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
    (u ut : Fin I.n → T → Fin (nu I + 1) → ℕ)
    (v vt : Fin I.m → T → Fin (nv I + 1) → ℕ)
    (h : BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) : BiLP5Feasible I X' s ℓ := by
  classical
  obtain ⟨hs, hl, _, _, h10a, h10b, h10c, h10e, h10f, h10g, h10i, h10j⟩ := h
  obtain ⟨⟨_, hvert, _, _⟩, hrt, _, hreach, _⟩ := hX
  refine ⟨hs, hl, ?_, ?_, h10i, h10j⟩
  · intro i
    let M : T → Prop := fun z => Sum.inl i ∈ X' z
    let A : T → ℕ := fun z => ∑ j ∈ J i z, I.r j i * ℓ (Sum.inr j) (Sum.inl i)
    obtain ⟨z, hz⟩ := hvert (Sum.inl i)
    obtain ⟨z0, hroot, _⟩ := TARooted.exists_root rt par hrt hreach M z hz
    have hc := h10c i z0 hroot
    have hacc := TARooted.acc_upper rt par hrt hreach M (fun z => bitVal (u i z))
      (fun z => bitVal (ut i z)) A (fun z hz => h10a i z hz) (fun z hz hnr => h10b i z hz hnr)
      z0 hroot.1
    have h1 : (∑ x ∈ Finset.univ.filter (TARooted.SubM par M z0), A x) ≤ ∑ x, A x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have h2 : (∑ x, A x) = ∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j),
        I.r j i * ℓ (Sum.inr j) (Sum.inl i) := part_sum_J I X' J Ip hJ i _
    have hc' : I.c i ≤ bitVal (u i z0) + (∑ c ∈ (TARooted.ch rt par z0).filter M, bitVal (ut i c)) +
        I.c i * s i := hc
    omega
  · intro j
    let M : T → Prop := fun z => Sum.inr j ∈ X' z
    let A : T → ℕ := fun z => ∑ i ∈ Ip j z, ℓ (Sum.inl i) (Sum.inr j)
    obtain ⟨z, hz⟩ := hvert (Sum.inr j)
    obtain ⟨z0, hroot, _⟩ := TARooted.exists_root rt par hrt hreach M z hz
    have hc := h10g j z0 hroot
    have hacc := TARooted.acc_upper rt par hrt hreach M (fun z => bitVal (v j z))
      (fun z => bitVal (vt j z)) A (fun z hz => h10e j z hz) (fun z hz hnr => h10f j z hz hnr)
      z0 hroot.1
    have h1 : (∑ x ∈ Finset.univ.filter (TARooted.SubM par M z0), A x) ≤ ∑ x, A x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    have h2 : (∑ x, A x) = ∑ i ∈ Finset.univ.filter (fun i => i ∈ I.e j),
        ℓ (Sum.inl i) (Sum.inr j) := part_sum_Ip I X' J Ip hJ j _
    have hc' : I.θ j - 1 ≤ bitVal (v j z0) + (∑ c ∈ (TARooted.ch rt par z0).filter M, bitVal (vt j c)) := hc
    omega

/-- (5) implies (10). -/
theorem ta_5_imp_10 (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip)
    (s : Fin I.n → ℕ) (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
    (h : BiLP5Feasible I X' s ℓ) :
    ∃ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt := by
  classical
  have hwalk := walks_M I t X' rt par hX
  obtain ⟨⟨htree, hvert, _, _⟩, hrt, hadj, hreach, _⟩ := hX
  obtain ⟨hs, hl, h5a, h5b, h5c, h5d⟩ := h
  let Mi : Fin I.n → T → Prop := fun i z => Sum.inl i ∈ X' z
  let Mj : Fin I.m → T → Prop := fun j z => Sum.inr j ∈ X' z
  let A : Fin I.n → T → ℕ := fun i z => ∑ j ∈ J i z, I.r j i * ℓ (Sum.inr j) (Sum.inl i)
  let B : Fin I.m → T → ℕ := fun j z => ∑ i ∈ Ip j z, ℓ (Sum.inl i) (Sum.inr j)
  let SA : Fin I.n → T → ℕ := fun i z =>
    ∑ x ∈ Finset.univ.filter (TARooted.SubM par (Mi i) z), A i x
  let SB : Fin I.m → T → ℕ := fun j z =>
    ∑ x ∈ Finset.univ.filter (TARooted.SubM par (Mj j) z), B j x
  have hcap : ∀ i, I.c i < 2 ^ (nu I + 1) := by
    intro i
    have h1 : I.c i ≤ Finset.univ.sup I.c := Finset.le_sup (Finset.mem_univ i)
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Finset.univ.sup I.c)
    unfold nu
    omega
  have hcapv : ∀ j, I.θ j - 1 < 2 ^ (nv I + 1) := by
    intro j
    have h1 : I.θ j ≤ Finset.univ.sup I.θ := Finset.le_sup (Finset.mem_univ j)
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Finset.univ.sup I.θ - 1)
    unfold nv
    omega
  have bu : ∀ i x, bitVal (bitsOf (nu I) (min x (I.c i))) = min x (I.c i) := fun i x =>
    bitVal_bitsOf _ _ (lt_of_le_of_lt (min_le_right _ _) (hcap i))
  have bv : ∀ j x, bitVal (bitsOf (nv I) (min x (I.θ j - 1))) = min x (I.θ j - 1) := fun j x =>
    bitVal_bitsOf _ _ (lt_of_le_of_lt (min_le_right _ _) (hcapv j))
  -- the subtree of a root contains every node of `T'_w`
  have hrootA : ∀ i z0, IsSubtreeRoot I X' rt par (Sum.inl i) z0 → SA i z0 = ∑ x, A i x := by
    intro i z0 hz0
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Finset.sum_eq_zero
    intro j hj
    exfalso
    apply hx
    have hMx : Mi i x := (hJ.1 i x j hj).2.1
    obtain ⟨z1, hr1, hs1⟩ := TARooted.exists_root rt par hrt hreach (Mi i) x hMx
    have := TARooted.root_unique t rt par hrt hadj hreach htree (Mi i)
      (fun a b ha hb => hwalk _ a b ha hb) hz0 hr1
    rw [this]; exact hs1
  have hrootB : ∀ j z0, IsSubtreeRoot I X' rt par (Sum.inr j) z0 → SB j z0 = ∑ x, B j x := by
    intro j z0 hz0
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Finset.sum_eq_zero
    intro i hi
    exfalso
    apply hx
    have hMx : Mj j x := (hJ.2.2.2.1 j x i hi).2.2
    obtain ⟨z1, hr1, hs1⟩ := TARooted.exists_root rt par hrt hreach (Mj j) x hMx
    have := TARooted.root_unique t rt par hrt hadj hreach htree (Mj j)
      (fun a b ha hb => hwalk _ a b ha hb) hz0 hr1
    rw [this]; exact hs1
  refine ⟨fun i z => bitsOf (nu I) (min (A i z) (I.c i)),
    fun i z => bitsOf (nu I) (min (SA i z) (I.c i)),
    fun j z => bitsOf (nv I) (min (B j z) (I.θ j - 1)),
    fun j z => bitsOf (nv I) (min (SB j z) (I.θ j - 1)), ?_⟩
  refine ⟨hs, hl, fun i z τ => ⟨bitsOf_le _ _ _, bitsOf_le _ _ _⟩,
    fun j z τ => ⟨bitsOf_le _ _ _, bitsOf_le _ _ _⟩, ?_, ?_, ?_, ?_, ?_, ?_, h5c, h5d⟩
  · -- (10a)
    intro i z _
    rw [bu]; exact min_le_left _ _
  · -- (10b)
    intro i z hz _
    rw [bu, bu]
    have := TARooted.capped_b rt par hrt hreach (Mi i) (A i) (I.c i) z hz
    refine le_trans this (le_of_eq ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [bu]
  · -- (10c)
    intro i z0 hz0
    rw [bu]
    have hsum : ∀ c ∈ (children rt par z0).filter (fun z' => Sum.inl i ∈ X' z'),
        bitVal (bitsOf (nu I) (min (SA i c) (I.c i))) = min (SA i c) (I.c i) :=
      fun c _ => bu i _
    rw [Finset.sum_congr rfl hsum]
    have hcb := TARooted.capped_b rt par hrt hreach (Mi i) (A i) (I.c i) z0 hz0.1
    have hroot := hrootA i z0 hz0
    have h5 := h5a i
    have h2 : (∑ x, A i x) = ∑ j ∈ Finset.univ.filter (fun j => i ∈ I.e j),
        I.r j i * ℓ (Sum.inr j) (Sum.inl i) := part_sum_J I X' J Ip hJ i _
    have hcb' : min (SA i z0) (I.c i) ≤ min (A i z0) (I.c i) +
        ∑ c ∈ (children rt par z0).filter (fun z' => Sum.inl i ∈ X' z'),
          min (SA i c) (I.c i) := hcb
    have hsi := hs i
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hsi with h0 | h1
    · rw [h0] at h5 ⊢
      have : min (SA i z0) (I.c i) = I.c i := by
        apply min_eq_right; omega
      omega
    · rw [h1]; omega
  · -- (10e)
    intro j z _
    rw [bv]; exact min_le_left _ _
  · -- (10f)
    intro j z hz _
    rw [bv, bv]
    have := TARooted.capped_b rt par hrt hreach (Mj j) (B j) (I.θ j - 1) z hz
    refine le_trans this (le_of_eq ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [bv]
  · -- (10g)
    intro j z0 hz0
    rw [bv]
    have hsum : ∀ c ∈ (children rt par z0).filter (fun z' => Sum.inr j ∈ X' z'),
        bitVal (bitsOf (nv I) (min (SB j c) (I.θ j - 1))) = min (SB j c) (I.θ j - 1) :=
      fun c _ => bv j _
    rw [Finset.sum_congr rfl hsum]
    have hcb := TARooted.capped_b rt par hrt hreach (Mj j) (B j) (I.θ j - 1) z0 hz0.1
    have hroot := hrootB j z0 hz0
    have h5 := h5b j
    have h2 : (∑ x, B j x) = ∑ i ∈ Finset.univ.filter (fun i => i ∈ I.e j),
        ℓ (Sum.inl i) (Sum.inr j) := part_sum_Ip I X' J Ip hJ j _
    have hcb' : min (SB j z0) (I.θ j - 1) ≤ min (B j z0) (I.θ j - 1) +
        ∑ c ∈ (children rt par z0).filter (fun z' => Sum.inr j ∈ X' z'),
          min (SB j c) (I.θ j - 1) := hcb
    have : min (SB j z0) (I.θ j - 1) = I.θ j - 1 := by
      apply min_eq_right; omega
    omega

end P8

theorem ta_prop8 (I : Instance) (hI : I.Standing) {T : Type} [Fintype T] [DecidableEq T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
    (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip) :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) ↔
        ∃ ℓ, BiLP5Feasible I X' s ℓ) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
        (u ut : Fin I.n → T → Fin (nu I + 1) → ℕ)
        (v vt : Fin I.m → T → Fin (nv I + 1) → ℕ),
      BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
          (u' ut' : Fin I.n → T → Fin (nu I + 1) → ℕ)
          (v' vt' : Fin I.m → T → Fin (nv I + 1) → ℕ),
        BiLP10Feasible I X' rt par J Ip s' ℓ' u' ut' v' vt' →
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
  refine ⟨?_, ?_⟩
  · intro s
    constructor
    · rintro ⟨ℓ, u, ut, v, vt, h⟩
      exact ⟨ℓ, ta_10_imp_5 I t X' rt par J Ip hX hJ s ℓ u ut v vt h⟩
    · rintro ⟨ℓ, h⟩
      obtain ⟨u, ut, v, vt, h10⟩ := ta_5_imp_10 I t X' rt par J Ip hX hJ s ℓ h
      exact ⟨ℓ, u, ut, v, vt, h10⟩
  · intro w s ℓ u ut v vt h hopt
    have h5 := ta_10_imp_5 I t X' rt par J Ip hX hJ s ℓ u ut v vt h
    have hfa := ta_feas5_imp I t X' hX.1 s ℓ h5
    refine ⟨hfa, ?_⟩
    rw [hsum w s h.1]
    apply le_antisymm
    · unfold OPT
      apply Finset.le_inf'
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      obtain ⟨ℓ', h'⟩ := ta_imp_feas5 I X' S hS hθ
      obtain ⟨u', ut', v', vt', h10'⟩ := ta_5_imp_10 I t X' rt par J Ip hX hJ _ ℓ' h'
      have := hopt _ ℓ' u' ut' v' vt' h10'
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
theorem solution (I : Instance) (hI : I.Standing) {T : Type} [Fintype T] [DecidableEq T]
    (t : SimpleGraph T) (X' : T → Finset (Fin I.n ⊕ Fin I.m)) (rt : T) (par : T → T)
    (J : Fin I.n → T → Finset (Fin I.m)) (Ip : Fin I.m → T → Finset (Fin I.n))
    (hX : IsRootedBinaryTD I t X' rt par) (hJ : IsPartitionData I X' J Ip) :
    (∀ s : Fin I.n → ℕ,
      (∃ ℓ u ut v vt, BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt) ↔
        ∃ ℓ, BiLP5Feasible I X' s ℓ) ∧
    (∀ (w : Fin I.n → ℝ) (s : Fin I.n → ℕ)
        (ℓ : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
        (u ut : Fin I.n → T → Fin (nu I + 1) → ℕ)
        (v vt : Fin I.m → T → Fin (nv I + 1) → ℕ),
      BiLP10Feasible I X' rt par J Ip s ℓ u ut v vt →
      (∀ (s' : Fin I.n → ℕ) (ℓ' : Fin I.n ⊕ Fin I.m → Fin I.n ⊕ Fin I.m → ℕ)
          (u' ut' : Fin I.n → T → Fin (nu I + 1) → ℕ)
          (v' vt' : Fin I.m → T → Fin (nv I + 1) → ℕ),
        BiLP10Feasible I X' rt par J Ip s' ℓ' u' ut' v' vt' →
          (∑ i, w i * (s i : ℝ)) ≤ ∑ i, w i * (s' i : ℝ)) →
      FullyActivates I (Finset.univ.filter (fun i => s i = 1)) ∧
      (∑ i, w i * (s i : ℝ)) = OPT I w) :=
  ta_prop8 I hI t X' rt par J Ip hX hJ
