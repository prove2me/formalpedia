-- Prove2me | solution 1 for TraceAdopt.LPReform.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:17:34.455301+00:00
-- url     : https://prove2.me/submissions/4c67d852-6ddc-440d-9595-71c73b5ffe3e

import Definitions.Def_TraceAdopt_LPReform_LinearSystem
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

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

namespace TAJT

open Finset

variable {n : ℕ}

/-- Restriction of a Boolean assignment to `D` (padded with `false`). -/
def rs (D : Finset (Fin n)) (z : Fin n → Bool) : Fin n → Bool :=
  fun u => if u ∈ D then z u else false

/-- Marginal of a function on assignments, on the coordinates `D`. -/
noncomputable def marg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (c : Fin n → Bool) : ℝ :=
  ∑ z, if rs D z = c then f z else 0

theorem rs_rs {D D' : Finset (Fin n)} (h : D ⊆ D') (z : Fin n → Bool) :
    rs D (rs D' z) = rs D z := by
  funext u
  simp only [rs]
  by_cases hu : u ∈ D
  · simp [hu, h hu]
  · simp [hu]

theorem rs_idem (D : Finset (Fin n)) (z : Fin n → Bool) : rs D (rs D z) = rs D z :=
  rs_rs subset_rfl z

theorem marg_marg {D D' : Finset (Fin n)} (h : D ⊆ D') (f : (Fin n → Bool) → ℝ)
    (c : Fin n → Bool) :
    marg D f c = ∑ c', if rs D c' = c then marg D' f c' else 0 := by
  unfold marg
  have : ∀ c', (if rs D c' = c then ∑ z, (if rs D' z = c' then f z else 0) else 0) =
      ∑ z, (if rs D' z = c' then (if rs D c' = c then f z else 0) else 0) := by
    intro c'
    split_ifs with h1
    · apply Finset.sum_congr rfl; intro z _; split_ifs <;> rfl
    · symm; apply Finset.sum_eq_zero; intro z _; split_ifs <;> rfl
  rw [Finset.sum_congr rfl (fun c' _ => this c'), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_ite_eq]
  simp [rs_rs h]

theorem marg_supp (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ a, rs D a ≠ a → f a = 0) (c : Fin n → Bool) : marg D f c = f c := by
  unfold marg
  by_cases hc : rs D c = c
  · rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro z _ hz
      split_ifs with h1
      · apply hf; rw [h1]; exact fun h => hz h.symm
      · rfl
    · simp
  · rw [hf c hc]
    apply Finset.sum_eq_zero
    intro z _
    split_ifs with h1
    · apply hf
      intro h2
      apply hc
      rw [← h1, rs_idem]
    · rfl

theorem marg_nonneg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (hf : ∀ a, 0 ≤ f a)
    (c : Fin n → Bool) : 0 ≤ marg D f c := by
  unfold marg
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hf z
  · exact le_rfl

theorem le_marg (D : Finset (Fin n)) (f : (Fin n → Bool) → ℝ) (hf : ∀ a, 0 ≤ f a)
    (z : Fin n → Bool) : f z ≤ marg D f (rs D z) := by
  unfold marg
  have : f z = if rs D z = rs D z then f z else 0 := by simp
  rw [this]
  apply Finset.single_le_sum (f := fun z' => if rs D z' = rs D z then f z' else 0)
  · intro z' _
    split_ifs
    · exact hf z'
    · exact le_rfl
  · exact Finset.mem_univ z

theorem marg_empty (f : (Fin n → Bool) → ℝ) (c : Fin n → Bool) :
    marg ∅ f c = if (fun _ => false) = c then ∑ z, f z else 0 := by
  unfold marg
  have : ∀ z : Fin n → Bool, rs ∅ z = fun _ => false := by
    intro z; funext u; simp [rs]
  simp only [this]
  split_ifs <;> simp

/-- Splitting a sum over assignments along one coordinate. -/
theorem sum_split (v : Fin n) (f : (Fin n → Bool) → ℝ) :
    ∑ z, f z = ∑ z ∈ univ.filter (fun z => z v = false),
      (f z + f (Function.update z v true)) := by
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun z => z v = false)]
  congr 1
  apply Finset.sum_nbij' (fun z => Function.update z v false) (fun z => Function.update z v true)
  · intro z hz; simp
  · intro z hz; simp at hz ⊢
  · intro z hz
    have hz' : z v = true := by simpa using hz
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz']
    · simp [Function.update_of_ne hu]
  · intro z hz
    have hz' : z v = false := by simpa using hz
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz']
    · simp [Function.update_of_ne hu]
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false] at hz
    congr 1
    funext u
    by_cases hu : u = v
    · subst hu; simp [hz]
    · simp [Function.update_of_ne hu]

theorem rs_update_of_not_mem (D : Finset (Fin n)) (z : Fin n → Bool) (v : Fin n) (b : Bool)
    (hv : v ∉ D) : rs D (Function.update z v b) = rs D z := by
  funext u
  simp only [rs]
  split_ifs with hu
  · have : u ≠ v := fun h => hv (h ▸ hu)
    simp [Function.update_of_ne this]
  · rfl

/-- Characterisation of `rs C z = c` through the separator `C.erase v`. -/
theorem rs_eq_iff (C : Finset (Fin n)) (v : Fin n) (hv : v ∈ C) (z c : Fin n → Bool)
    (hc : rs C c = c) :
    rs C z = c ↔ rs (C.erase v) z = rs (C.erase v) c ∧ z v = c v := by
  constructor
  · intro h
    subst h
    refine ⟨(rs_rs (Finset.erase_subset v C) z).symm, ?_⟩
    simp [rs, hv]
  · rintro ⟨h1, h2⟩
    funext u
    by_cases huv : u = v
    · subst huv
      have : rs C c u = c u := by rw [hc]
      simp only [rs, hv, if_true] at this ⊢
      exact h2
    · by_cases huC : u ∈ C
      · have hu : u ∈ C.erase v := Finset.mem_erase.2 ⟨huv, huC⟩
        have := congrFun h1 u
        simp only [rs, hu, if_true] at this
        simp only [rs, huC, if_true]
        exact this
      · have : rs C c u = c u := by rw [hc]
        simp only [rs, huC, if_false] at this ⊢
        exact this

/-- The separator marginal is the sum of the two extensions. -/
theorem marg_pair (C : Finset (Fin n)) (v : Fin n) (hv : v ∈ C) (f : (Fin n → Bool) → ℝ)
    (hf : ∀ a, rs C a ≠ a → f a = 0) (z : Fin n → Bool) :
    marg (C.erase v) f (rs (C.erase v) z) =
      f (rs C (Function.update z v false)) + f (rs C (Function.update z v true)) := by
  have hvS : v ∉ C.erase v := Finset.notMem_erase v C
  unfold marg
  rw [sum_split v]
  set a0 := rs C (Function.update z v false) with ha0
  have ha0v : a0 v = false := by simp [ha0, rs, hv]
  have ha0C : rs C a0 = a0 := by rw [ha0, rs_idem]
  have ha0S : rs (C.erase v) a0 = rs (C.erase v) z := by
    rw [ha0, rs_rs (Finset.erase_subset v C), rs_update_of_not_mem _ _ _ _ hvS]
  have ha0t : Function.update a0 v true = rs C (Function.update z v true) := by
    funext u
    by_cases huv : u = v
    · subst huv; simp [rs, hv]
    · simp only [Function.update_of_ne huv, ha0, rs]
  rw [Finset.sum_eq_single a0]
  · rw [rs_update_of_not_mem _ _ _ _ hvS, ha0S, ha0t]
    simp
  · intro a ha hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [rs_update_of_not_mem _ _ _ _ hvS]
    split_ifs with h1
    · -- `a` agrees with `z` on the separator but differs from `a0`
      have hnot : rs C a ≠ a := by
        intro hC
        apply hne
        rw [← hC, rs_eq_iff C v hv a a0 ha0C]
        refine ⟨by rw [h1, ha0S], ?_⟩
        rw [ha, ha0v]
      have hnot' : rs C (Function.update a v true) ≠ Function.update a v true := by
        intro hC
        apply hnot
        funext u
        by_cases huC : u ∈ C
        · simp [rs, huC]
        · have := congrFun hC u
          have huv : u ≠ v := fun h => huC (h ▸ hv)
          simp only [rs, huC, if_false, Function.update_of_ne huv] at this
          simp only [rs, huC, if_false]
          exact this
      rw [hf a hnot, hf _ hnot']
      simp
    · simp
  · intro h
    exfalso; apply h
    simp [ha0v]

/-- Gluing locally consistent distributions along an elimination ordering. -/
theorem glue (rk : Fin n → ℕ) (hrk : Function.Injective rk) (C : Fin n → Finset (Fin n))
    (hCv : ∀ v, v ∈ C v) (hCr : ∀ v, ∀ u ∈ C v, rk v ≤ rk u) (π : Fin n → Fin n)
    (hπ : ∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v))
    (lam : Fin n → (Fin n → Bool) → ℝ) (hnn : ∀ v a, 0 ≤ lam v a)
    (hsupp : ∀ v a, rs (C v) a ≠ a → lam v a = 0) (hsum : ∀ v, ∑ a, lam v a = 1)
    (hcons : ∀ v, ((C v).erase v).Nonempty → ∀ c,
      marg ((C v).erase v) (lam v) c = marg ((C v).erase v) (lam (π v)) c) :
    ∃ μ : (Fin n → Bool) → ℝ, (∀ z, 0 ≤ μ z) ∧ (∑ z, μ z = 1) ∧
      ∀ v c, marg (C v) μ c = lam v c := by
  classical
  let P : ℕ → Prop := fun θ => ∃ μ : (Fin n → Bool) → ℝ, (∀ z, 0 ≤ μ z) ∧ (∑ z, μ z = 1) ∧
    (∀ z, (∃ u, rk u < θ ∧ z u = true) → μ z = 0) ∧
    ∀ v, θ ≤ rk v → ∀ c, marg (C v) μ c = lam v c
  let B := Finset.univ.sup rk + 1
  have hB : ∀ v, rk v < B := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have base : P B := by
    refine ⟨fun z => if z = (fun _ => false) then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro z; dsimp only; split_ifs <;> norm_num
    · simp
    · rintro z ⟨u, _, hu⟩
      have : z ≠ fun _ => false := by
        intro h; rw [h] at hu; exact Bool.false_ne_true hu
      simp [this]
    · intro v hv; exact absurd hv (Nat.not_le.2 (hB v))
  have step : ∀ θ, P (θ + 1) → P θ := by
    intro θ ⟨μ, hμ0, hμ1, hμs, hμm⟩
    by_cases hex : ∃ v0, rk v0 = θ
    swap
    · push Not at hex
      refine ⟨μ, hμ0, hμ1, fun z ⟨u, hu, hzu⟩ => hμs z ⟨u, by omega, hzu⟩, ?_⟩
      intro v hv c
      apply hμm v _ c
      have := hex v
      omega
    obtain ⟨v0, hv0⟩ := hex
    set S := (C v0).erase v0 with hS
    have hv0C := hCv v0
    have hv0S : v0 ∉ S := Finset.notMem_erase v0 (C v0)
    let m : (Fin n → Bool) → ℝ := fun c => marg S (lam v0) c
    -- (F1) the separator marginal of `μ` is `m`
    have F1 : ∀ c, marg S μ c = m c := by
      intro c
      by_cases hSne : S.Nonempty
      · obtain ⟨hlt, hsub⟩ := hπ v0 hSne
        have hm := hμm (π v0) (by omega)
        rw [marg_marg hsub μ c]
        simp only [m]
        rw [hcons v0 hSne c, marg_marg hsub (lam (π v0)) c]
        apply Finset.sum_congr rfl
        intro c' _
        rw [hm c', marg_supp _ _ (hsupp (π v0)) c']
      · rw [Finset.not_nonempty_iff_eq_empty] at hSne
        simp only [m]
        rw [hSne, marg_empty, marg_empty, hμ1, hsum v0]
    -- (F3) `μ` vanishes where `m` does
    have F3 : ∀ z, m (rs S z) = 0 → μ z = 0 := by
      intro z hz
      have h1 := le_marg S μ hμ0 z
      rw [F1, hz] at h1
      exact le_antisymm h1 (hμ0 z)
    have hlam_le : ∀ c, lam v0 c ≤ m (rs S c) := fun c => le_marg S (lam v0) (hnn v0) c
    let μ' : (Fin n → Bool) → ℝ := fun z =>
      μ (Function.update z v0 false) * lam v0 (rs (C v0) z) / m (rs S z)
    have hm0 : ∀ c, 0 ≤ m c := fun c => marg_nonneg S (lam v0) (hnn v0) c
    have F0 : ∀ z, 0 ≤ μ' z := fun z =>
      div_nonneg (mul_nonneg (hμ0 _) (hnn _ _)) (hm0 _)
    have hμv0 : ∀ z, z v0 = true → μ z = 0 := by
      intro z hz; exact hμs z ⟨v0, by omega, hz⟩
    have hzz : ∀ z : Fin n → Bool, z v0 = false → Function.update z v0 false = z := by
      intro z hz
      funext u; by_cases hu : u = v0
      · subst hu; simp [hz]
      · simp [Function.update_of_ne hu]
    -- (F4) marginals on sets avoiding `v0` are unchanged
    have F4 : ∀ D : Finset (Fin n), v0 ∉ D → ∀ c, marg D μ' c = marg D μ c := by
      intro D hD c
      unfold marg
      rw [sum_split v0, sum_split v0]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [rs_update_of_not_mem _ _ _ _ hD, hμv0 (Function.update z v0 true) (by simp)]
      split_ifs with hc
      · simp only [μ']
        rw [Function.update_idem, hzz z hz, rs_update_of_not_mem _ _ _ _ hv0S, ← add_div,
          ← mul_add]
        have hpair := marg_pair (C v0) v0 hv0C (lam v0) (hsupp v0) z
        rw [← hS, hzz z hz] at hpair
        rw [← hpair, add_zero]
        by_cases hmz : m (rs S z) = 0
        · rw [F3 z hmz]; simp
        · field_simp; rfl
      · simp
    -- (F5) the new marginal
    have F5 : ∀ c, marg (C v0) μ' c = lam v0 c := by
      intro c
      by_cases hc : rs (C v0) c = c
      swap
      · rw [hsupp v0 c hc]
        unfold marg
        apply Finset.sum_eq_zero
        intro z _
        split_ifs with h
        · exfalso; apply hc; rw [← h, rs_idem]
        · rfl
      have hval : ∀ z, rs (C v0) z = c → μ' z =
          μ (Function.update z v0 false) * (lam v0 c / m (rs S c)) := by
        intro z hz
        simp only [μ']
        have : rs S z = rs S c := by
          rw [← hz, hS, rs_rs (Finset.erase_subset v0 (C v0))]
        rw [hz, this]
        ring
      have hsum' : (∑ z, if rs (C v0) z = c then μ (Function.update z v0 false) else 0) =
          m (rs S c) := by
        rw [← F1]
        unfold marg
        rw [sum_split v0, sum_split v0]
        apply Finset.sum_congr rfl
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [hμv0 (Function.update z v0 true) (by simp), rs_update_of_not_mem _ _ _ _ hv0S,
          Function.update_idem, hzz z hz]
        have ha := rs_eq_iff (C v0) v0 hv0C z c hc
        have hb := rs_eq_iff (C v0) v0 hv0C (Function.update z v0 true) c hc
        rw [← hS] at ha hb
        rw [rs_update_of_not_mem _ _ _ _ hv0S] at hb
        simp only [Function.update_self] at hb
        by_cases h1 : rs S z = rs S c
        · cases hcv : c v0
          · have e1 : rs (C v0) z = c := ha.2 ⟨h1, by rw [hz, hcv]⟩
            have e2 : ¬ rs (C v0) (Function.update z v0 true) = c := by
              intro h; have := (hb.1 h).2; rw [hcv] at this; exact Bool.noConfusion this
            simp [e1, e2, h1]
          · have e1 : ¬ rs (C v0) z = c := by
              intro h; have := (ha.1 h).2; rw [hz, hcv] at this; exact Bool.noConfusion this
            have e2 : rs (C v0) (Function.update z v0 true) = c := hb.2 ⟨h1, by rw [hcv]⟩
            simp [e1, e2, h1]
        · have e1 : ¬ rs (C v0) z = c := fun h => h1 (ha.1 h).1
          have e2 : ¬ rs (C v0) (Function.update z v0 true) = c := fun h => h1 (hb.1 h).1
          simp [e1, e2, h1]
      unfold marg
      have : (∑ z, if rs (C v0) z = c then μ' z else 0) =
          (∑ z, if rs (C v0) z = c then μ (Function.update z v0 false) else 0) *
            (lam v0 c / m (rs S c)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · exact hval z h
        · simp
      rw [this, hsum']
      by_cases hmz : m (rs S c) = 0
      · have : lam v0 c = 0 := le_antisymm (by rw [← hmz]; exact hlam_le c) (hnn v0 c)
        rw [this, hmz]; simp
      · field_simp
    refine ⟨μ', F0, ?_, ?_, ?_⟩
    · have h1 := F4 ∅ (Finset.notMem_empty v0) (fun _ => false)
      rw [marg_empty, marg_empty] at h1
      simp only [if_true] at h1
      rw [h1, hμ1]
    · rintro z ⟨u, hu, hzu⟩
      have huv : u ≠ v0 := by intro h; subst h; omega
      simp only [μ']
      rw [hμs _ ⟨u, by omega, by rwa [Function.update_of_ne huv]⟩]
      simp
    · intro v hv c
      by_cases hvv : v = v0
      · subst hvv; exact F5 c
      · have hlt : θ + 1 ≤ rk v := by
          have : rk v ≠ θ := fun h => hvv (hrk (h.trans hv0.symm))
          omega
        have hv0Cv : v0 ∉ C v := by
          intro h
          have := hCr v v0 h
          omega
        rw [F4 (C v) hv0Cv c, hμm v hlt c]
  have all : ∀ k, k ≤ B → P (B - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using base
    | succ k ih =>
      intro hk
      have := ih (by omega)
      have e : B - k = (B - (k + 1)) + 1 := by omega
      rw [e] at this
      exact step _ this
  obtain ⟨μ, h0, h1, _, h3⟩ := all B le_rfl
  exact ⟨μ, h0, h1, fun v c => h3 v (by simp) c⟩

end TAJT

namespace TAElim

open SimpleGraph

/-- An elimination structure of width `ω` extracted from a tree decomposition. -/
theorem elim_of_td {n : ℕ} (G : SimpleGraph (Fin n)) (ω : ℕ)
    (hG : RobertsonSeymour1986.GM5.TreewidthLE G ω) :
    ∃ (rk : Fin n → ℕ) (C : Fin n → Finset (Fin n)) (π : Fin n → Fin n),
      Function.Injective rk ∧ (∀ v, v ∈ C v) ∧ (∀ v, ∀ u ∈ C v, rk v ≤ rk u) ∧
      (∀ v, (C v).card ≤ ω + 1) ∧
      (∀ v, ((C v).erase v).Nonempty → rk v < rk (π v) ∧ (C v).erase v ⊆ C (π v)) ∧
      (∀ K : Finset (Fin n), K.Nonempty → (∀ u ∈ K, ∀ w ∈ K, u ≠ w → G.Adj u w) →
        ∃ v, K ⊆ C v) := by
  classical
  obtain ⟨T, hT, t, X, ⟨htree, hcov, hedge, hpath⟩, hw⟩ := hG
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun _ => 0, fun _ => ∅, id, fun a => a.elim0, fun v => v.elim0, fun v => v.elim0,
      fun v => v.elim0, fun v => v.elim0, ?_⟩
    rintro K ⟨v, _⟩; exact v.elim0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  haveI : Nonempty T := htree.connected.nonempty
  let r : T := Classical.arbitrary T
  let L : T → ℕ := fun y => (TAChordal.P htree r y).length
  have hz : ∀ v : Fin n, ∃ z, v ∈ X z ∧ ∀ w, v ∈ X w → L z ≤ L w := by
    intro v
    obtain ⟨y0, hy0⟩ := hcov v
    obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun w => v ∈ X w)) L
      ⟨y0, by simp [hy0]⟩
    exact ⟨z, by simpa using hz, fun w hw => hmin w (by simp [hw])⟩
  choose zv hzvX hzvmin using hz
  let d : Fin n → ℕ := fun v => L (zv v)
  let Bd : ℕ := Finset.univ.sup d + 1
  have hdB : ∀ v, d v < Bd := fun v => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  let rk : Fin n → ℕ := fun v => v.val + (Bd - d v) * n
  have hrkinj : Function.Injective rk := by
    intro a b hab
    have h1 : rk a % n = a.val := by
      simp only [rk]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
    have h2 : rk b % n = b.val := by
      simp only [rk]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]
    apply Fin.ext
    rw [← h1, ← h2, hab]
  have hrkd : ∀ v u, rk v < rk u → d u ≤ d v := by
    intro v u h
    by_contra hcon
    push Not at hcon
    have h1 : Bd - d u + 1 ≤ Bd - d v := by have := hdB u; omega
    have h2 : (Bd - d u + 1) * n ≤ (Bd - d v) * n := Nat.mul_le_mul_right n h1
    have h3 : rk u < (Bd - d u + 1) * n := by
      simp only [rk]; rw [Nat.add_mul, Nat.one_mul]; have := u.isLt; omega
    have h4 : (Bd - d v) * n ≤ rk v := by simp only [rk]; omega
    omega
  let C : Fin n → Finset (Fin n) := fun v => insert v ((X (zv v)).filter (fun u => rk v < rk u))
  have hCsub : ∀ v, C v ⊆ X (zv v) := by
    intro v u hu
    simp only [C, Finset.mem_insert, Finset.mem_filter] at hu
    rcases hu with rfl | ⟨hu, _⟩
    · exact hzvX u
    · exact hu
  -- the key comparison
  have key : ∀ (y : T) (v u : Fin n), v ∈ X y → u ∈ X y → d u ≤ d v → u ∈ X (zv v) := by
    intro y v u hvy huy hle
    have h1 := TAChordal.F htree X hpath r v (zv v) y (hzvX v) (hzvmin v) hvy
    have h2 := TAChordal.F htree X hpath r u (zv u) y (hzvX u) (hzvmin u) huy
    have h3 := TAChordal.order htree X hpath r y (zv v) (zv u) h1 h2 hle
    exact hpath y (zv v) (zv u) _ ((TAChordal.P_isPath htree r y).takeUntil h2) h3
      (Finset.mem_inter.2 ⟨huy, hzvX u⟩)
  let π : Fin n → Fin n := fun v =>
    if h : ((C v).erase v).Nonempty then
      Classical.choose (Finset.exists_min_image ((C v).erase v) rk h) else v
  refine ⟨rk, C, π, hrkinj, fun v => Finset.mem_insert_self _ _, ?_, ?_, ?_, ?_⟩
  · intro v u hu
    simp only [C, Finset.mem_insert, Finset.mem_filter] at hu
    rcases hu with rfl | ⟨_, h⟩
    · exact le_rfl
    · exact h.le
  · intro v
    exact le_trans (Finset.card_le_card (hCsub v)) (hw _)
  · intro v hS
    have hspec := Classical.choose_spec (Finset.exists_min_image ((C v).erase v) rk hS)
    have hπv : π v = Classical.choose (Finset.exists_min_image ((C v).erase v) rk hS) := by
      simp only [π, dif_pos hS]
    rw [hπv]
    set w := Classical.choose (Finset.exists_min_image ((C v).erase v) rk hS)
    obtain ⟨hwS, hwmin⟩ := hspec
    have hwC : w ∈ C v := Finset.mem_of_mem_erase hwS
    have hwv : w ≠ v := Finset.ne_of_mem_erase hwS
    have hrvw : rk v < rk w := by
      simp only [C, Finset.mem_insert, Finset.mem_filter] at hwC
      rcases hwC with h | ⟨_, h⟩
      · exact absurd h hwv
      · exact h
    refine ⟨hrvw, ?_⟩
    intro u hu
    have huC : u ∈ C v := Finset.mem_of_mem_erase hu
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    by_cases huw : u = w
    · rw [huw]; exact Finset.mem_insert_self _ _
    have hlt : rk w < rk u := lt_of_le_of_ne (hwmin u hu) (fun h => huw (hrkinj h).symm)
    have huX : u ∈ X (zv v) := hCsub v huC
    have hwX : w ∈ X (zv v) := hCsub v hwC
    have := key (zv v) w u hwX huX (hrkd w u hlt)
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr ⟨this, hlt⟩
  · intro K hK hclq
    obtain ⟨v, hvK, hvmin⟩ := Finset.exists_min_image K rk hK
    refine ⟨v, fun u hu => ?_⟩
    by_cases huv : u = v
    · rw [huv]; exact Finset.mem_insert_self _ _
    have hlt : rk v < rk u := lt_of_le_of_ne (hvmin u hu) (fun h => huv (hrkinj h).symm)
    obtain ⟨y, hvy, huy⟩ := hedge v u (hclq v hvK u hu (Ne.symm huv))
    have := key y v u hvy huy (hrkd v u hlt)
    simp only [C, Finset.mem_insert, Finset.mem_filter]
    exact Or.inr ⟨this, hlt⟩

end TAElim

namespace TALP

open TraceAdopt.LPReform

/-- A finite linear system indexed by arbitrary finite types, in Fin-matrix form. -/
theorem to_matrix {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (rowX : κ → Fin n → ℝ) (rowY : κ → ι → ℝ) (rhs : κ → ℝ) :
    ∃ (A' : Matrix (Fin (Fintype.card κ)) (Fin n ⊕ Fin (Fintype.card ι)) ℝ)
      (b' : Fin (Fintype.card κ) → ℝ),
      {x : Fin n → ℝ | ∃ y : Fin (Fintype.card ι) → ℝ, LinFeasible A' b' x y} =
        {x | ∃ y : ι → ℝ, ∀ r, rhs r ≤ (∑ i, rowX r i * x i) + ∑ j, rowY r j * y j} := by
  classical
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  refine ⟨fun r v => Sum.elim (fun i => rowX (eκ.symm r) i) (fun j => rowY (eκ.symm r) (eι.symm j)) v,
    fun r => rhs (eκ.symm r), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, LinFeasible, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨y', hy'⟩
    refine ⟨fun j => y' (eι j), fun r => ?_⟩
    have := hy' (eκ r)
    simp only [Equiv.symm_apply_apply] at this
    convert this using 2
    rw [← Equiv.sum_comp eι.symm]
    simp
  · rintro ⟨y, hy⟩
    refine ⟨fun j => y (eι.symm j), fun r => ?_⟩
    have := hy (eκ.symm r)
    convert this using 2
    rw [← Equiv.sum_comp eι]
    simp

theorem proj_convex {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (rowX : κ → Fin n → ℝ) (rowY : κ → ι → ℝ) (rhs : κ → ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∃ y : ι → ℝ, ∀ r, rhs r ≤ (∑ i, rowX r i * x i) + ∑ j, rowY r j * y j} := by
  intro x hx x' hx' a b ha hb hab
  obtain ⟨y, hy⟩ := hx
  obtain ⟨y', hy'⟩ := hx'
  refine ⟨a • y + b • y', fun r => ?_⟩
  have h1 := hy r
  have h2 := hy' r
  have e : (∑ i, rowX r i * (a • x + b • x') i) + ∑ j, rowY r j * (a • y + b • y') j =
      a * ((∑ i, rowX r i * x i) + ∑ j, rowY r j * y j) +
        b * ((∑ i, rowX r i * x' i) + ∑ j, rowY r j * y' j) := by
    have e1 : ∀ i, rowX r i * (a • x + b • x') i = a * (rowX r i * x i) + b * (rowX r i * x' i) := by
      intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have e2 : ∀ j, rowY r j * (a • y + b • y') j = a * (rowY r j * y j) + b * (rowY r j * y' j) := by
      intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [e]
  have : rhs r = a * rhs r + b * rhs r := by rw [← add_mul, hab, one_mul]
  rw [this]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

end TALP

namespace TAP4

open TraceAdopt.LPReform TAJT

variable {n : ℕ}

/-- Real indicator vector of a Boolean assignment. -/
def bval (z : Fin n → Bool) : Fin n → ℝ := fun i => if z i then 1 else 0

theorem sum_sigma_fst {β : Fin n → Type} [∀ v, Fintype (β v)] (v : Fin n)
    (f : (Σ v, β v) → ℝ) :
    (∑ j, if j.1 = v then f j else 0) = ∑ a : β v, f ⟨v, a⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single v]
  · simp
  · intro w _ hw; simp [hw]
  · simp

theorem sum_subtype_dite (p : (Fin n → Bool) → Prop) [DecidablePred p]
    (g : {a // p a} → ℝ) :
    (∑ a : {a // p a}, g a) = ∑ a, if h : p a then g ⟨a, h⟩ else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]
  have h2 : (∑ a ∈ Finset.univ.filter (fun a => ¬ p a), if h : p a then g ⟨a, h⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp [ha]
  rw [h2, add_zero]
  rw [Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  simp [a.2]

theorem sum_marg (D : Finset (Fin n)) (μ : (Fin n → Bool) → ℝ) (h : (Fin n → Bool) → ℝ) :
    (∑ a, h a * marg D μ a) = ∑ z, μ z * h (rs D z) := by
  unfold marg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (rs D z)]
  · simp [mul_comm]
  · intro a _ ha
    rw [if_neg (Ne.symm ha), mul_zero]
  · simp

/-- Auxiliary variables: one per node `v` and local assignment on `C v`. -/
abbrev Iota (C : Fin n → Finset (Fin n)) := Σ v : Fin n, {a : Fin n → Bool // rs (C v) a = a}

/-- Separator assignments. -/
abbrev Sep (C : Fin n → Finset (Fin n)) :=
  Σ v : Fin n, {c : Fin n → Bool // rs ((C v).erase v) c = c}

/-- Constraint indices. -/
abbrev Kappa (C : Fin n → Finset (Fin n)) :=
  Iota C ⊕ Iota C ⊕ (Fin n × Bool) ⊕ (Fin n × Bool) ⊕ (Sep C × Bool)

def sg (s : Bool) : ℝ := if s then 1 else -1

theorem sg_ne (s : Bool) : sg s ≠ 0 := by cases s <;> simp [sg]

def rowX (C : Fin n → Finset (Fin n)) : Kappa C → Fin n → ℝ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s)))) => fun i => if i = v then sg s else 0
  | _ => fun _ => 0

open Classical in
noncomputable def rowY (C : Fin n → Finset (Fin n)) (π : Fin n → Fin n)
    (Loc : Fin n → (Fin n → Bool) → Prop) : Kappa C → Iota C → ℝ
  | Sum.inl j => fun j' => if j' = j then 1 else 0
  | Sum.inr (Sum.inl j) => fun j' => if j' = j ∧ ¬ Loc j.1 j.2.1 then -1 else 0
  | Sum.inr (Sum.inr (Sum.inl (v, s))) => fun j' => if j'.1 = v then sg s else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s)))) => fun j' =>
      if j'.1 = v ∧ j'.2.1 v = true then -sg s else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨v, c⟩, s)))) => fun j' =>
      if ((C v).erase v).Nonempty then
        sg s * ((if j'.1 = v ∧ rs ((C v).erase v) j'.2.1 = c.1 then 1 else 0) -
          (if j'.1 = π v ∧ rs ((C v).erase v) j'.2.1 = c.1 then 1 else 0))
      else 0

def rhs (C : Fin n → Finset (Fin n)) : Kappa C → ℝ
  | Sum.inr (Sum.inr (Sum.inl (_, s))) => sg s
  | _ => 0

/-- Reading the linear system. -/
theorem feas_iff (C : Fin n → Finset (Fin n)) (π : Fin n → Fin n)
    (Loc : Fin n → (Fin n → Bool) → Prop) (x : Fin n → ℝ) (y : Iota C → ℝ) :
    (∀ r, rhs C r ≤ (∑ i, rowX C r i * x i) + ∑ j, rowY C π Loc r j * y j) ↔
      (∀ j, 0 ≤ y j) ∧ (∀ j, ¬ Loc j.1 j.2.1 → y j ≤ 0) ∧
      (∀ v, (∑ j, if j.1 = v then y j else 0) = 1) ∧
      (∀ v, x v = ∑ j, if j.1 = v ∧ j.2.1 v = true then y j else 0) ∧
      (∀ v, ((C v).erase v).Nonempty → ∀ c, rs ((C v).erase v) c = c →
        (∑ j, if j.1 = v ∧ rs ((C v).erase v) j.2.1 = c then y j else 0) =
          ∑ j, if j.1 = π v ∧ rs ((C v).erase v) j.2.1 = c then y j else 0) := by
  classical
  simp only [Sum.forall, Prod.forall]
  have hR1 : ∀ j, (rhs C (Sum.inl j) ≤ (∑ i, rowX C (Sum.inl j) i * x i) +
      ∑ j', rowY C π Loc (Sum.inl j) j' * y j') ↔ 0 ≤ y j := by
    intro j
    simp [rhs, rowX, rowY]
  have hR2 : ∀ j, (rhs C (Sum.inr (Sum.inl j)) ≤ (∑ i, rowX C (Sum.inr (Sum.inl j)) i * x i) +
      ∑ j', rowY C π Loc (Sum.inr (Sum.inl j)) j' * y j') ↔ (¬ Loc j.1 j.2.1 → y j ≤ 0) := by
    intro j
    by_cases hL : Loc j.1 j.2.1
    · simp [rhs, rowX, rowY, hL]
    · simp [rhs, rowX, rowY, hL]
  have hsum3 : ∀ v s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inl (v, s)))) j' * y j') =
      sg s * ∑ j, if j.1 = v then y j else 0 := by
    intro v s
    simp only [rowY, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hsum4 : ∀ v s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s))))) j' * y j') =
      -(sg s * ∑ j, if j.1 = v ∧ j.2.1 v = true then y j else 0) := by
    intro v s
    simp only [rowY, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hx4 : ∀ v s, (∑ i, rowX C (Sum.inr (Sum.inr (Sum.inr (Sum.inl (v, s))))) i * x i) =
      sg s * x v := by
    intro v s
    simp [rowX]
  have hsum5 : ∀ v c s, (∑ j', rowY C π Loc (Sum.inr (Sum.inr (Sum.inr (Sum.inr (⟨v, c⟩, s))))) j' * y j') =
      if ((C v).erase v).Nonempty then
        sg s * ((∑ j, if j.1 = v ∧ rs ((C v).erase v) j.2.1 = c.1 then y j else 0) -
          ∑ j, if j.1 = π v ∧ rs ((C v).erase v) j.2.1 = c.1 then y j else 0) else 0 := by
    intro v c s
    simp only [rowY]
    split_ifs with hne
    · rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · simp
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun j => (hR1 j).1 (h1 j), fun j => (hR2 j).1 (h2 j), ?_, ?_, ?_⟩
    · intro v
      have a := h3 v true
      have b := h3 v false
      rw [hsum3] at a b
      simp [rhs, rowX, sg] at a b
      linarith
    · intro v
      have a := h4 v true
      have b := h4 v false
      rw [hx4, hsum4] at a b
      simp [rhs, sg] at a b
      linarith
    · intro v hne c hc
      have a := h5 ⟨v, ⟨c, hc⟩⟩ true
      have b := h5 ⟨v, ⟨c, hc⟩⟩ false
      rw [hsum5] at a b
      simp [rhs, rowX, hne, sg] at a b
      linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun j => (hR1 j).2 (h1 j), fun j => (hR2 j).2 (h2 j), ?_, ?_, ?_⟩
    · intro v s
      rw [hsum3, h3 v]
      simp [rhs, rowX]
    · intro v s
      rw [hx4, hsum4, ← h4 v]
      simp [rhs]
    · rintro ⟨v, c, hc⟩ s
      rw [hsum5]
      split_ifs with hne
      · rw [h5 v hne c hc]; simp [rhs, rowX]
      · simp [rhs, rowX]

end TAP4

namespace TAP4

open TraceAdopt.LPReform TAJT

theorem card_sub_le {n : ℕ} (D : Finset (Fin n)) :
    Fintype.card {a : Fin n → Bool // rs D a = a} ≤ 2 ^ D.card := by
  classical
  have : Fintype.card {a : Fin n → Bool // rs D a = a} ≤ Fintype.card (D → Bool) := by
    apply Fintype.card_le_of_injective (fun a => fun u => a.1 u.1)
    intro a b hab
    apply Subtype.ext
    rw [← a.2, ← b.2]
    funext u
    simp only [rs]
    split_ifs with hu
    · exact congrFun hab ⟨u, hu⟩
    · rfl
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using this

theorem ta_prop4 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (b : Fin m → ℝ) (ω : ℕ),
        RobertsonSeymour1986.GM5.TreewidthLE
          (intersectionGraph
            (fun k : Fin m => Finset.univ.filter (fun i : Fin n => A k i ≠ 0))) ω →
        ∃ (N K : ℕ) (A' : Matrix (Fin K) (Fin n ⊕ Fin N) ℝ)
          (b' : Fin K → ℝ),
          n + N + K ≤ C * 2 ^ ω * (n + 1) ∧
          {x : Fin n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A' b' x y} =
            convexHull ℝ {x : Fin n → ℝ |
              (∀ i, x i = 0 ∨ x i = 1) ∧
              ∀ k, b k ≤ A.mulVec x k} := by
  refine ⟨13, by norm_num, ?_⟩
  intro n m A b ω hTW
  classical
  set F := {x : Fin n → ℝ | (∀ i, x i = 0 ∨ x i = 1) ∧ ∀ k, b k ≤ A.mulVec x k} with hF
  have h2pos : 1 ≤ 2 ^ ω := Nat.one_le_two_pow
  by_cases hbad : ∃ k, (∀ i, A k i = 0) ∧ 0 < b k
  · obtain ⟨k, hk0, hkb⟩ := hbad
    refine ⟨0, 1, 0, fun _ => 1, ?_, ?_⟩
    · nlinarith
    · have hFe : F = ∅ := by
        ext x
        simp only [hF, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h
        have := h k
        simp [Matrix.mulVec, dotProduct, hk0] at this
        linarith
      rw [hFe, convexHull_empty]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro y hy
      have := hy 0
      simp at this
      linarith
  push Not at hbad
  obtain ⟨rk, C, π, hrk, hCv, hCr, hCc, hπ, hclq⟩ := TAElim.elim_of_td _ ω hTW
  let rowOK : Fin m → (Fin n → Bool) → Prop := fun k z => b k ≤ ∑ i, A k i * bval z i
  let Loc : Fin n → (Fin n → Bool) → Prop := fun v a =>
    ∀ k, (Finset.univ.filter (fun i => A k i ≠ 0)) ⊆ C v → rowOK k a
  have hrowC : ∀ k v (z : Fin n → Bool), (Finset.univ.filter (fun i => A k i ≠ 0)) ⊆ C v →
      (∑ i, A k i * bval (rs (C v) z) i) = ∑ i, A k i * bval z i := by
    intro k v z hsub
    apply Finset.sum_congr rfl
    intro i _
    by_cases hA : A k i = 0
    · simp [hA]
    · have : i ∈ C v := hsub (by simp [hA])
      simp [bval, rs, this]
  obtain ⟨A', b', hAb⟩ := TALP.to_matrix (rowX C) (rowY C π Loc) (rhs C)
  refine ⟨Fintype.card (Iota C), Fintype.card (Kappa C), A', b', ?_, ?_⟩
  · -- size
    have hI : Fintype.card (Iota C) ≤ n * (2 * 2 ^ ω) := by
      rw [Fintype.card_sigma]
      calc (∑ v, Fintype.card {a : Fin n → Bool // rs (C v) a = a})
          ≤ ∑ _v : Fin n, 2 * 2 ^ ω := by
            apply Finset.sum_le_sum
            intro v _
            refine le_trans (card_sub_le (C v)) ?_
            rw [← pow_succ']
            exact Nat.pow_le_pow_right (by norm_num) (hCc v)
        _ = n * (2 * 2 ^ ω) := by simp
    have hS : Fintype.card (Sep C) ≤ n * 2 ^ ω := by
      rw [Fintype.card_sigma]
      calc (∑ v, Fintype.card {c : Fin n → Bool // rs ((C v).erase v) c = c})
          ≤ ∑ _v : Fin n, 2 ^ ω := by
            apply Finset.sum_le_sum
            intro v _
            refine le_trans (card_sub_le _) ?_
            apply Nat.pow_le_pow_right (by norm_num)
            rw [Finset.card_erase_of_mem (hCv v)]
            have := hCc v
            omega
        _ = n * 2 ^ ω := by simp
    have hK : Fintype.card (Kappa C) = 2 * Fintype.card (Iota C) + 4 * n +
        2 * Fintype.card (Sep C) := by
      simp only [Kappa, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      ring
    rw [hK]
    nlinarith
  · rw [hAb]
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := (feas_iff C π Loc x y).1 hy
      let lam : Fin n → (Fin n → Bool) → ℝ := fun v a =>
        if h : rs (C v) a = a then y ⟨v, ⟨a, h⟩⟩ else 0
      have conv : ∀ v (g : (Fin n → Bool) → ℝ),
          (∑ a, g a * lam v a) = ∑ j : Iota C, if j.1 = v then g j.2.1 * y j else 0 := by
        intro v g
        rw [sum_sigma_fst v (fun j : Iota C => g j.2.1 * y j),
          sum_subtype_dite (fun a => rs (C v) a = a) (fun a => g a.1 * y ⟨v, a⟩)]
        apply Finset.sum_congr rfl
        intro a _
        simp only [lam]
        split_ifs <;> simp
      have hnn : ∀ v a, 0 ≤ lam v a := by
        intro v a; simp only [lam]; split_ifs
        · exact h1 _
        · exact le_rfl
      have hsupp : ∀ v a, rs (C v) a ≠ a → lam v a = 0 := by
        intro v a h; simp [lam, h]
      have hsum : ∀ v, ∑ a, lam v a = 1 := by
        intro v
        have := conv v (fun _ => 1)
        simp only [one_mul] at this
        rw [this]; exact h3 v
      have hmarg : ∀ (D : Finset (Fin n)) w c, marg D (lam w) c =
          ∑ j : Iota C, if j.1 = w ∧ rs D j.2.1 = c then y j else 0 := by
        intro D w c
        unfold marg
        have e1 : (∑ a, if rs D a = c then lam w a else 0) =
            ∑ a, (if rs D a = c then (1 : ℝ) else 0) * lam w a := by
          apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
        rw [e1, conv w]
        apply Finset.sum_congr rfl
        intro j _
        by_cases ha : j.1 = w <;> by_cases hb : rs D j.2.1 = c <;> simp [ha, hb]
      have hcons : ∀ v, ((C v).erase v).Nonempty → ∀ c,
          marg ((C v).erase v) (lam v) c = marg ((C v).erase v) (lam (π v)) c := by
        intro v hne c
        by_cases hc : rs ((C v).erase v) c = c
        · rw [hmarg, hmarg]; exact h5 v hne c hc
        · have hz : ∀ f, marg ((C v).erase v) f c = 0 := by
            intro f
            unfold marg
            apply Finset.sum_eq_zero
            intro a _
            split_ifs with h
            · exfalso; apply hc; rw [← h, rs_idem]
            · rfl
          rw [hz, hz]
      obtain ⟨μ, hμ0, hμ1, hμm⟩ := glue rk hrk C hCv hCr π hπ lam hnn hsupp hsum hcons
      have hx : x = ∑ z, μ z • bval z := by
        funext v
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h4 v]
        have e1 := conv v (fun a => bval a v)
        have e2 : (∑ j : Iota C, if j.1 = v ∧ j.2.1 v = true then y j else 0) =
            ∑ j : Iota C, if j.1 = v then bval j.2.1 v * y j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases ha : j.1 = v <;> by_cases hb : j.2.1 v = true <;> simp [ha, hb, bval]
        rw [e2, ← e1]
        have e3 : (∑ a, bval a v * lam v a) = ∑ a, bval a v * marg (C v) μ a := by
          apply Finset.sum_congr rfl; intro a _; rw [hμm]
        rw [e3, sum_marg]
        apply Finset.sum_congr rfl
        intro z _
        simp [bval, rs, hCv v]
      have hmem : ∀ z, 0 < μ z → bval z ∈ F := by
        intro z hz
        refine ⟨fun i => by unfold bval; split_ifs <;> simp, ?_⟩
        intro k
        by_cases hk : ∀ i, A k i = 0
        · have : A.mulVec (bval z) k = 0 := by
            simp [Matrix.mulVec, dotProduct, hk]
          rw [this]; exact hbad k hk
        push Not at hk
        obtain ⟨i0, hi0⟩ := hk
        obtain ⟨v, hv⟩ := hclq (Finset.univ.filter (fun i => A k i ≠ 0)) ⟨i0, by simp [hi0]⟩
          (by
            intro u hu w hw huw
            exact ⟨huw, k, hu, hw⟩)
        have hpos : 0 < lam v (rs (C v) z) := by
          have := le_marg (C v) μ hμ0 z
          rw [hμm] at this
          linarith
        have hL : Loc v (rs (C v) z) := by
          by_contra hL
          have := h2 ⟨v, ⟨rs (C v) z, rs_idem _ _⟩⟩ hL
          have e : lam v (rs (C v) z) = y ⟨v, ⟨rs (C v) z, rs_idem _ _⟩⟩ := by
            simp [lam, rs_idem]
          linarith
        have := hL k hv
        simp only [rowOK] at this
        rw [hrowC k v z hv] at this
        simpa [Matrix.mulVec, dotProduct] using this
      have hfil : ∀ (f : (Fin n → Bool) → (Fin n → ℝ)),
          (∑ z, μ z • f z) = ∑ z ∈ Finset.univ.filter (fun z => 0 < μ z), μ z • f z := by
        intro f
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · rfl
        · have : μ z = 0 := le_antisymm (not_lt.1 h) (hμ0 z)
          simp [this]
      have hfil1 : (∑ z ∈ Finset.univ.filter (fun z => 0 < μ z), μ z) = 1 := by
        rw [← hμ1, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs with h
        · rfl
        · exact (le_antisymm (not_lt.1 h) (hμ0 z)).symm
      rw [hx, hfil]
      apply (convex_convexHull ℝ F).sum_mem
      · intro z _; exact hμ0 z
      · exact hfil1
      · intro z hz
        exact subset_convexHull ℝ F (hmem z (by simpa using hz))
    · apply convexHull_min _ (TALP.proj_convex _ _ _)
      intro x hx
      obtain ⟨hbin, hrows⟩ := hx
      let z : Fin n → Bool := fun i => decide (x i = 1)
      have hz : bval z = x := by
        funext i
        rcases hbin i with h | h <;> simp [bval, z, h]
      let y : Iota C → ℝ := fun j => if j.2.1 = rs (C j.1) z then 1 else 0
      have key : ∀ w (P : (Fin n → Bool) → Prop) [DecidablePred P],
          (∑ j : Iota C, if j.1 = w ∧ P j.2.1 then y j else 0) =
            if P (rs (C w) z) then 1 else 0 := by
        intro w P _
        have e : (∑ j : Iota C, if j.1 = w ∧ P j.2.1 then y j else 0) =
            ∑ j : Iota C, if j.1 = w then (if P j.2.1 then y j else 0) else 0 := by
          apply Finset.sum_congr rfl; intro j _
          by_cases ha : j.1 = w <;> simp [ha]
        rw [e, sum_sigma_fst w (fun j : Iota C => if P j.2.1 then y j else 0)]
        rw [Finset.sum_eq_single ⟨rs (C w) z, rs_idem _ _⟩]
        · simp [y]
        · intro a _ ha
          have : a.1 ≠ rs (C w) z := fun h => ha (Subtype.ext h)
          simp [y, this]
        · simp
      have hrowsz : ∀ k, rowOK k z := by
        intro k
        have := hrows k
        simp only [rowOK, hz]
        simpa [Matrix.mulVec, dotProduct] using this
      refine ⟨y, (feas_iff C π Loc x y).2 ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · intro j; simp only [y]; split_ifs <;> norm_num
      · intro j hL
        simp only [y]
        split_ifs with h
        · exfalso; apply hL
          rw [h]
          intro k hk
          simp only [rowOK]
          rw [hrowC k j.1 z hk]
          exact hrowsz k
        · exact le_rfl
      · intro v
        have := key v (fun _ => True)
        simpa using this
      · intro v
        rw [key v (fun a => a v = true)]
        conv_lhs => rw [← hz]
        simp [bval, rs, hCv v]
      · intro v hne c _
        rw [key v (fun a => rs ((C v).erase v) a = c), key (π v) (fun a => rs ((C v).erase v) a = c),
          rs_rs (Finset.erase_subset v (C v)), rs_rs (hπ v hne).2]

end TAP4

open TraceAdopt.LPReform in
theorem solution :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
        (b : Fin m → ℝ) (ω : ℕ),
        RobertsonSeymour1986.GM5.TreewidthLE
          (intersectionGraph
            (fun k : Fin m => Finset.univ.filter (fun i : Fin n => A k i ≠ 0))) ω →
        ∃ (N K : ℕ) (A' : Matrix (Fin K) (Fin n ⊕ Fin N) ℝ)
          (b' : Fin K → ℝ),
          n + N + K ≤ C * 2 ^ ω * (n + 1) ∧
          {x : Fin n → ℝ | ∃ y : Fin N → ℝ, LinFeasible A' b' x y} =
            convexHull ℝ {x : Fin n → ℝ |
              (∀ i, x i = 0 ∨ x i = 1) ∧
              ∀ k, b k ≤ A.mulVec x k} :=
  TAP4.ta_prop4
