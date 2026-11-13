-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:18:11.753501+00:00
-- url     : https://prove2.me/submissions/f9dcc47a-49f4-4916-a704-90b7406dd634

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_LittleCharity_MMS_Setting

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS
/-! Blueprint for Lemma 3.2 (Seddighin–Seddighin, EC 2025, Lemma 8.1).

Guiding structure: `q` permutations `σ a` of `Fin N` with `σ a ^ (k+1) = 1` such that no reduced
word of length in `[1, g)` fixes a point (a free action of the free product of `q` copies of
`ℤ/(k+1)` with injectivity radius `g`).  Seeds are the points of `Fin N`; the allocation node of
agent `a` at seed `s` is the `σ a`-orbit of `s`, represented by `rep a s`.  A labelling
`ℓ : Fin q × Fin N → Fin t` gives node `(a, rep a s)` the bundle `f a ⁻¹' {ℓ (a, rep a s)}`. -/
/-- A reduced word: exponents in `[1, k]`, consecutive letters with distinct generators. -/
def Reduced (q k : ℕ) (w : List (Fin q × ℕ)) : Prop :=
  (∀ p ∈ w, 1 ≤ p.2 ∧ p.2 ≤ k) ∧ w.IsChain (fun p p' => p.1 ≠ p'.1)

/-- The permutation a word denotes. -/
def act {N q : ℕ} (σ : Fin q → Equiv.Perm (Fin N)) (w : List (Fin q × ℕ)) : Equiv.Perm (Fin N) :=
  (w.map (fun p => σ p.1 ^ p.2)).prod

/-- A guiding structure with girth `g`. -/
structure Guide (q k g N : ℕ) where
  σ : Fin q → Equiv.Perm (Fin N)
  pow_eq : ∀ a, σ a ^ (k + 1) = 1
  girth : ∀ w : List (Fin q × ℕ), w ≠ [] → w.length < g → Reduced q k w →
    ∀ s, act σ w s ≠ s

end SubadditiveMMS580.Amplification.Dev.SS
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartG
open Equiv
variable {q k : ℕ}
/-! High-girth guiding structures (`exists_guide`), by iterated voltage lifts with voltages in
`(Fin q × X → ZMod 2)`: the lift of a girth-`g` structure (`g ≥ 2`) has girth `g + 1`, because for a
reduced word `w = w' ++ [(a, d)]` of length `≤ g` acting on `(s, z)`, the edge `(a, σ_a^d s)` is hit
exactly once by the voltage sum (all suffixes of `w'` are shorter than `g`). -/
/-- `act` for an arbitrary type of points. -/
def actX {X : Type} (σ : Fin q → Perm X) (w : List (Fin q × ℕ)) : Perm X :=
  (w.map (fun p => σ p.1 ^ p.2)).prod

lemma actX_cons {X : Type} (σ : Fin q → Perm X) (l : Fin q × ℕ) (w : List (Fin q × ℕ)) :
    actX σ (l :: w) = σ l.1 ^ l.2 * actX σ w := by
  simp [actX]

lemma actX_append {X : Type} (σ : Fin q → Perm X) (u v : List (Fin q × ℕ)) :
    actX σ (u ++ v) = actX σ u * actX σ v := by
  simp [actX]

/-- Guide property for an arbitrary type of points. -/
def IsG (q k g : ℕ) {X : Type} (σ : Fin q → Perm X) : Prop :=
  (∀ a, σ a ^ (k + 1) = 1) ∧
    ∀ w : List (Fin q × ℕ), w ≠ [] → w.length < g → Reduced q k w → ∀ s, actX σ w s ≠ s

lemma reduced_infix {w v : List (Fin q × ℕ)} (h : Reduced q k w) (hv : v <:+: w) :
    Reduced q k v :=
  ⟨fun p hp => h.1 p (hv.subset hp), h.2.infix hv⟩

lemma IsG.mono {g g' : ℕ} {X : Type} {σ : Fin q → Perm X} (h : IsG q k g σ) (hg : g' ≤ g) :
    IsG q k g' σ :=
  ⟨h.1, fun w hw hl hr s => h.2 w hw (by omega) hr s⟩

end SubadditiveMMS580.Amplification.Dev.SS.PartG
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartG
open Equiv
variable {q k : ℕ}
variable {X A : Type} [AddCommGroup A] (σ : Fin q → Perm X) (μ : Fin q → X → A)
/-- The voltage lift of `σ a`. -/
def liftPerm (a : Fin q) : Perm (X × A) where
  toFun x := (σ a x.1, x.2 + μ a (σ a x.1) - μ a x.1)
  invFun x := ((σ a).symm x.1, x.2 + μ a ((σ a).symm x.1) - μ a x.1)
  left_inv x := by
    rcases x with ⟨s, z⟩
    ext
    · simp
    · simp only [Equiv.symm_apply_apply]; abel
  right_inv x := by
    rcases x with ⟨s, z⟩
    ext
    · simp
    · simp only [Equiv.apply_symm_apply]; abel

lemma liftPerm_pow (a : Fin q) (d : ℕ) (s : X) (z : A) :
    (liftPerm σ μ a ^ d) (s, z) = ((σ a ^ d) s, z + μ a ((σ a ^ d) s) - μ a s) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ' (σ a), Perm.mul_apply]
    ext
    · rfl
    · simp only [liftPerm, coe_fn_mk]; abel

/-- Voltage of a word started at `s`. -/
def D : List (Fin q × ℕ) → X → A
  | [], _ => 0
  | l :: w, s => D w s + μ l.1 ((σ l.1 ^ l.2) (actX σ w s)) - μ l.1 (actX σ w s)

lemma actX_lift (w : List (Fin q × ℕ)) (s : X) (z : A) :
    actX (liftPerm σ μ) w (s, z) = (actX σ w s, z + D σ μ w s) := by
  induction w with
  | nil => simp [actX, D]
  | cons l w ih =>
    rw [actX_cons, Perm.mul_apply, ih, liftPerm_pow, actX_cons, Perm.mul_apply]
    ext
    · rfl
    · simp only [D]; abel

lemma D_append (u v : List (Fin q × ℕ)) (s : X) :
    D σ μ (u ++ v) s = D σ μ u (actX σ v s) + D σ μ v s := by
  induction u with
  | nil => simp [D]
  | cons l u ih =>
    simp only [List.cons_append, D, ih, actX_append, Perm.mul_apply]; abel

end SubadditiveMMS580.Amplification.Dev.SS.PartG
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartG
open Equiv
variable {q k : ℕ}
variable {X : Type} [DecidableEq X] (σ : Fin q → Perm X)
/-- The `ZMod 2` voltages: indicator of the edge `(a, x)`. -/
def μ0 (a : Fin q) (x : X) : Fin q × X → ZMod 2 := Pi.single (a, x) 1

lemma D_eval_zero (e : Fin q × X) (p : X) (u : List (Fin q × ℕ))
    (h : ∀ u1 l u2, u = u1 ++ l :: u2 →
      (l.1, actX σ u2 p) ≠ e ∧ (l.1, actX σ (l :: u2) p) ≠ e) :
    D σ (μ0 (q := q)) u p e = 0 := by
  induction u with
  | nil => rfl
  | cons l u ih =>
    have ih' := ih (fun u1 l' u2 hu => h (l :: u1) l' u2 (by rw [hu]; rfl))
    obtain ⟨h1, h2⟩ := h [] l u rfl
    rw [actX_cons, Perm.mul_apply] at h2
    simp only [D, Pi.sub_apply, Pi.add_apply, ih', μ0, Pi.single_apply, Ne.symm h1,
      Ne.symm h2, if_false]
    simp

theorem isG_lift {g : ℕ} (hg : 2 ≤ g) (h : IsG q k g σ) :
    IsG q k (g + 1) (liftPerm σ (μ0 (q := q))) := by
  refine ⟨fun a => ?_, fun w hw hlen hred x hfix => ?_⟩
  · refine Equiv.ext fun x => ?_
    rcases x with ⟨s, z⟩
    rw [liftPerm_pow, h.1 a]
    simp
  · rcases x with ⟨s, z⟩
    obtain ⟨w', l, rfl⟩ : ∃ w' l, w = w' ++ [l] :=
      ⟨w.dropLast, w.getLast hw, (List.dropLast_append_getLast hw).symm⟩
    rw [actX_lift] at hfix
    have hD : D σ μ0 (w' ++ [l]) s = 0 := by
      have := congrArg Prod.snd hfix
      simpa using this
    set p2 := (σ l.1 ^ l.2) s with hp2
    have hlen' : w'.length + 1 ≤ g := by simpa using hlen
    -- girth facts
    have hs : p2 ≠ s := by
      have := h.2 [l] (by simp) (by simp; omega)
        (reduced_infix hred (List.suffix_append w' [l]).isInfix) s
      simpa [actX] using this
    have hZ : D σ μ0 w' p2 (l.1, p2) = 0 := by
      apply D_eval_zero
      intro u1 l' u2 hu
      subst hu
      have hinf : l' :: u2 <:+: u1 ++ l' :: u2 ++ [l] := List.infix_append _ _ _
      refine ⟨?_, ?_⟩
      · by_cases h0 : u2 = []
        · subst h0
          have hc := hred.2
          rw [List.append_assoc, List.singleton_append, List.isChain_split] at hc
          have hc2 : List.IsChain (fun p p' : Fin q × ℕ => p.1 ≠ p'.1) [l', l] := hc.2
          have hne : l'.1 ≠ l.1 := by simpa using hc2
          intro heq
          exact hne (Prod.mk.inj heq).1
        · intro heq
          have := h.2 u2 h0 (by simp at hlen'; omega)
            (reduced_infix hred ((List.suffix_cons l' u2).isInfix.trans hinf)) p2
          exact this (congrArg Prod.snd heq)
      · intro heq
        have := h.2 (l' :: u2) (by simp) (by simp at hlen' ⊢; omega)
          (reduced_infix hred hinf) p2
        exact this (congrArg Prod.snd heq)
    have hval := congrFun hD (l.1, p2)
    rw [D_append] at hval
    have hl : actX σ [l] s = p2 := by simp [actX, hp2]
    rw [hl, Pi.add_apply, hZ] at hval
    simp only [D, actX, List.map_nil, List.prod_nil, Perm.one_apply, μ0, Pi.add_apply,
      Pi.sub_apply, Pi.single_apply, ← hp2, if_true, Pi.zero_apply] at hval
    have hs' : ((l.1, p2) = (l.1, s)) = False := by simp [hs]
    simp [hs'] at hval

end SubadditiveMMS580.Amplification.Dev.SS.PartG
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartG
open Equiv
variable {q k : ℕ}
lemma addRight_pow_apply (d : ℕ) (x : ZMod (k + 1)) :
    (Equiv.addRight (1 : ZMod (k + 1)) ^ d) x = x + d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', Perm.mul_apply, ih, coe_addRight]; push_cast; ring

theorem isG_base :
    IsG q k 2 (fun _ : Fin q => Equiv.addRight (1 : ZMod (k + 1))) := by
  refine ⟨fun a => ?_, fun w hw hlen hred x hfix => ?_⟩
  · refine Equiv.ext fun x => ?_
    rw [addRight_pow_apply, ZMod.natCast_self, add_zero]; rfl
  · match w, hw, hlen with
    | [l], _, _ =>
      simp only [actX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        addRight_pow_apply] at hfix
      have h0 : ((l.2 : ℕ) : ZMod (k + 1)) = 0 := by
        have := congrArg (fun y => y - x) hfix
        simpa using this
      rw [ZMod.natCast_eq_zero_iff] at h0
      have h1 := hred.1 l (by simp)
      have := Nat.le_of_dvd (by omega) h0
      omega
    | _ :: _ :: _, _, hlen => simp at hlen

theorem exists_isG (m : ℕ) :
    ∃ (X : Type) (_ : Finite X) (_ : Nonempty X) (σ : Fin q → Perm X), IsG q k (m + 2) σ := by
  induction m with
  | zero => exact ⟨ZMod (k + 1), inferInstance, inferInstance, _, isG_base⟩
  | succ m ih =>
    classical
    obtain ⟨X, _, _, σ, hσ⟩ := ih
    exact ⟨X × (Fin q × X → ZMod 2), inferInstance, inferInstance, _,
      isG_lift σ (by omega) hσ⟩

theorem exists_guide (q k g : ℕ) (hk : 1 ≤ k) : ∃ N, 0 < N ∧ Nonempty (Guide q k g N) := by
  obtain ⟨X, _, _, σ, hσ⟩ := exists_isG (q := q) (k := k) g
  have hσ' := hσ.mono (g' := g) (by omega)
  let e := Finite.equivFin X
  refine ⟨Nat.card X, Nat.card_pos, ⟨Guide.mk (fun a => e.permCongrHom (σ a)) ?_ ?_⟩⟩
  · intro a
    rw [← map_pow, hσ'.1 a, map_one]
  · intro w hw hlen hred s hfix
    have hact : act (fun a => e.permCongrHom (σ a)) w = e.permCongrHom (actX σ w) := by
      unfold act actX
      rw [map_list_prod, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      exact (map_pow e.permCongrHom _ _).symm
    rw [hact] at hfix
    change e.permCongr (actX σ w) s = s at hfix
    rw [Equiv.permCongr_apply] at hfix
    apply hσ'.2 w hw hlen hred (e.symm s)
    apply e.injective
    rw [hfix, Equiv.apply_symm_apply]

end SubadditiveMMS580.Amplification.Dev.SS.PartG
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS
alias exists_guide := SubadditiveMMS580.Amplification.Dev.SS.PartG.exists_guide

end SubadditiveMMS580.Amplification.Dev.SS
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS
variable {q k g N : ℕ}
/-- Canonical representative of the `σ a`-orbit of `s`. -/
def rep (G : Guide q k g N) (a : Fin q) (s : Fin N) : Fin N :=
  ((Finset.range (k + 1)).image (fun e => (G.σ a ^ e) s)).min'
    (by simp)

/-- Node `(a, rep a s)` holds item `x` under labelling `ℓ` and partitions `f`. -/
def active {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (a : Fin q) (s : Fin N) : Prop :=
  ℓ (a, rep G a s) = f a x

/-- A chain step list from a node of agent `prev`: `(a, d)` moves from the current seed `p` to
`p' = (σ prev ^ d) p` and then to the node of agent `a` at `p'`. The first step may use any
`d ≤ k`, later steps `1 ≤ d ≤ k`; consecutive agents differ. -/
def ChainOK (k : ℕ) {q : ℕ} : Fin q → Bool → List (Fin q × ℕ) → Prop
  | _, _, [] => True
  | prev, first, (a, d) :: rest =>
    a ≠ prev ∧ (if first then d ≤ k else 1 ≤ d ∧ d ≤ k) ∧ ChainOK k a false rest

/-- Every node a chain visits (after the start) is active. -/
def ChainActive {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) : Fin q → Fin N → List (Fin q × ℕ) → Prop
  | _, _, [] => True
  | prev, p, (a, d) :: rest =>
    active G f ℓ x a ((G.σ prev ^ d) p) ∧ ChainActive G f ℓ x a ((G.σ prev ^ d) p) rest

/-- Node `(a, s)` is `R`-good for item `x`: every active chain from it has length `< R`. -/
def Good {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (R : ℕ) (a : Fin q) (s : Fin N) : Prop :=
  ∀ c : List (Fin q × ℕ), ChainOK k a true c → ChainActive G f ℓ x a s c → c.length < R

end SubadditiveMMS580.Amplification.Dev.SS
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartB
variable {q k g N : ℕ}
/-! ### Orbits (copied from `SSGive`) -/
/-- The `σ a`-orbit of `s` (as a finset of seeds). -/
def orb (G : Guide q k g N) (a : Fin q) (s : Fin N) : Finset (Fin N) :=
  (Finset.range (k + 1)).image (fun e => (G.σ a ^ e) s)

lemma pow_mod_eq (G : Guide q k g N) (a : Fin q) (n : ℕ) :
    G.σ a ^ n = G.σ a ^ (n % (k + 1)) := by
  conv_lhs => rw [← Nat.div_add_mod n (k + 1), pow_add, pow_mul, G.pow_eq a, one_pow, one_mul]

lemma mem_orb (G : Guide q k g N) (a : Fin q) (s t : Fin N) :
    t ∈ orb G a s ↔ ∃ n : ℕ, (G.σ a ^ n) s = t := by
  unfold orb
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨e, -, he⟩
    exact ⟨e, he⟩
  · rintro ⟨n, hn⟩
    exact ⟨n % (k + 1), Nat.mod_lt _ (Nat.succ_pos _), by rw [← pow_mod_eq]; exact hn⟩

lemma self_mem_orb (G : Guide q k g N) (a : Fin q) (s : Fin N) : s ∈ orb G a s :=
  (mem_orb G a s s).2 ⟨0, by simp⟩

lemma orb_eq_of_mem (G : Guide q k g N) (a : Fin q) (s t : Fin N) (h : t ∈ orb G a s) :
    orb G a t = orb G a s := by
  obtain ⟨n, rfl⟩ := (mem_orb G a s t).1 h
  ext u
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m + n, by rw [pow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m + n * k, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    have : m + n * k + n = m + (k + 1) * n := by ring
    rw [this, pow_add, pow_mul, G.pow_eq, one_pow, mul_one]

lemma rep_eq_of_orb_eq (G : Guide q k g N) (a : Fin q) (s t : Fin N)
    (h : orb G a s = orb G a t) : rep G a s = rep G a t := by
  show (orb G a s).min' _ = (orb G a t).min' _
  congr 1

lemma rep_mem (G : Guide q k g N) (a : Fin q) (s : Fin N) : rep G a s ∈ orb G a s :=
  Finset.min'_mem _ _

lemma exists_of_rep_eq (G : Guide q k g N) (b : Fin q) (p p0 : Fin N)
    (h : rep G b p = rep G b p0) : ∃ n, n < k + 1 ∧ (G.σ b ^ n) p = p0 := by
  have h1 : orb G b p = orb G b p0 := by
    rw [← orb_eq_of_mem G b p _ (rep_mem G b p), ← orb_eq_of_mem G b p0 _ (rep_mem G b p0), h]
  have : p0 ∈ orb G b p := h1 ▸ self_mem_orb G b p0
  unfold orb at this
  obtain ⟨e, he, he'⟩ := Finset.mem_image.1 this
  exact ⟨e, Finset.mem_range.1 he, he'⟩

/-! ### Nodes visited by a chain -/
/-- The nodes a chain visits after its start. -/
def nodes (G : Guide q k g N) : Fin q → Fin N → List (Fin q × ℕ) → List (Fin q × Fin N)
  | _, _, [] => []
  | prev, p, (a, d) :: rest =>
    (a, rep G a ((G.σ prev ^ d) p)) :: nodes G a ((G.σ prev ^ d) p) rest

lemma length_nodes (G : Guide q k g N) :
    ∀ (prev : Fin q) (p : Fin N) (c : List (Fin q × ℕ)), (nodes G prev p c).length = c.length
  | _, _, [] => rfl
  | _, _, (a, _) :: rest => by simp [nodes, length_nodes G a _ rest]

lemma chainActive_nodes {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) :
    ∀ (prev : Fin q) (p : Fin N) (c : List (Fin q × ℕ)), ChainActive G f ℓ x prev p c →
      ∀ u ∈ nodes G prev p c, ℓ u = f u.1 x
  | _, _, [], _ => by simp [nodes]
  | prev, p, (a, d) :: rest, h => by
    intro u hu
    simp only [nodes, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact h.1
    · exact chainActive_nodes G f ℓ x a _ rest h.2 u hu

lemma chainOK_take :
    ∀ (c : List (Fin q × ℕ)) (prev : Fin q) (first : Bool) (n : ℕ), ChainOK k prev first c →
      ChainOK k prev first (c.take n)
  | [], _, _, _, _ => by simp [ChainOK]
  | _ :: _, _, _, 0, _ => by simp [ChainOK]
  | (a, _) :: rest, _, _, n + 1, h => ⟨h.1, h.2.1, chainOK_take rest a false n h.2.2⟩

lemma chainActive_take {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) :
    ∀ (c : List (Fin q × ℕ)) (prev : Fin q) (p : Fin N) (n : ℕ), ChainActive G f ℓ x prev p c →
      ChainActive G f ℓ x prev p (c.take n)
  | [], _, _, _, _ => by simp [ChainActive]
  | _ :: _, _, _, 0, _ => by simp [ChainActive]
  | (a, _) :: rest, _, _, n + 1, h => ⟨h.1, chainActive_take G f ℓ x rest a _ n h.2⟩

/-! ### Distinctness from girth -/
lemma act_cons (G : Guide q k g N) (b : Fin q) (n : ℕ) (w : List (Fin q × ℕ)) :
    act G.σ ((b, n) :: w) = G.σ b ^ n * act G.σ w := by
  simp [act]

lemma reduced_cons (b : Fin q) (n : ℕ) (w : List (Fin q × ℕ)) (hn1 : 1 ≤ n) (hnk : n ≤ k)
    (hred : Reduced q k w) (hhd : ∀ y ∈ w.head?, y.1 ≠ b) : Reduced q k ((b, n) :: w) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hn1, hnk⟩
    · exact hred.1 p hp
  · rw [List.isChain_cons]
    exact ⟨fun y hy => (hhd y hy).symm, hred.2⟩

lemma head_case (G : Guide q k g N) (b : Fin q) (p0 : Fin N) (a : Fin q) (p : Fin N)
    (w : List (Fin q × ℕ)) (hw : act G.σ w p0 = p) (hred : Reduced q k w)
    (hne : w = [] → a ≠ b) (hhd : ∀ y ∈ w.head?, y.1 ≠ a) (hlen : w.length + 1 < g)
    (h : (b, rep G b p0) = (a, rep G a p)) : False := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have hw0 : w ≠ [] := fun h0 => hne h0 rfl
  obtain ⟨n, hn, hnp⟩ := exists_of_rep_eq G b p p0 h.symm
  by_cases hn0 : n = 0
  · subst hn0
    simp only [pow_zero, Equiv.Perm.coe_one, id] at hnp
    exact G.girth w hw0 (by omega) hred p0 (hw.trans hnp)
  · apply G.girth ((b, n) :: w) (by simp) (by simp; omega)
      (reduced_cons b n w (by omega) (by omega) hred hhd) p0
    rw [act_cons, Equiv.Perm.mul_apply, hw, hnp]

lemma noret (G : Guide q k g N) (b : Fin q) (p0 : Fin N) :
    ∀ (c : List (Fin q × ℕ)) (a : Fin q) (p : Fin N) (w : List (Fin q × ℕ)),
      ChainOK k a false c → act G.σ w p0 = p → Reduced q k w → (w = [] → a ≠ b) →
      (∀ y ∈ w.head?, y.1 ≠ a) → w.length + c.length + 1 < g →
      (b, rep G b p0) ∉ (a, rep G a p) :: nodes G a p c := by
  intro c
  induction c with
  | nil =>
    intro a p w _ hw hred hne hhd hlen hmem
    simp only [nodes, List.mem_singleton] at hmem
    exact head_case G b p0 a p w hw hred hne hhd (by simpa using hlen) hmem
  | cons ad rest ih =>
    obtain ⟨a', d⟩ := ad
    intro a p w hc hw hred hne hhd hlen hmem
    rcases List.mem_cons.1 hmem with h | h
    · exact head_case G b p0 a p w hw hred hne hhd (by simp at hlen; omega) h
    · simp only [nodes] at h
      obtain ⟨hc1, hc2, hc3⟩ := hc
      simp only [Bool.false_eq_true, if_false] at hc2
      exact ih a' ((G.σ a ^ d) p) ((a, d) :: w) hc3
        (by rw [act_cons, Equiv.Perm.mul_apply, hw])
        (reduced_cons a d w hc2.1 hc2.2 hred hhd) (by simp)
        (by simpa using hc1.symm) (by simp at hlen ⊢; omega) h

lemma nodup_nodes (G : Guide q k g N) :
    ∀ (c : List (Fin q × ℕ)) (prev : Fin q) (p : Fin N) (first : Bool),
      ChainOK k prev first c → c.length + 1 < g →
      ((prev, rep G prev p) :: nodes G prev p c).Nodup
  | [], _, _, _, _, _ => by simp [nodes]
  | (a, d) :: rest, prev, p, first, hc, hlen => by
    have hlen' : rest.length + 1 < g := by simp at hlen; omega
    simp only [nodes]
    refine List.nodup_cons.2 ⟨?_, nodup_nodes G rest a _ false hc.2.2 hlen'⟩
    have hrep : rep G prev p = rep G prev ((G.σ prev ^ d) p) :=
      rep_eq_of_orb_eq G prev _ _ (orb_eq_of_mem G prev p _ ((mem_orb G _ _ _).2 ⟨d, rfl⟩)).symm
    rw [hrep]
    exact noret G prev _ rest a _ [] hc.2.2 rfl ⟨by simp, List.isChain_nil⟩ (fun _ => hc.1)
      (by simp) (by simpa using hlen')

/-! ### Counting chains -/
/-- All candidate step lists of length `n` from agent `prev`. -/
def chains (k : ℕ) {q : ℕ} : Fin q → Bool → ℕ → Finset (List (Fin q × ℕ))
  | _, _, 0 => {[]}
  | prev, first, n + 1 =>
    ((Finset.univ.filter (fun a : Fin q => a ≠ prev)) ×ˢ
        (if first then Finset.range (k + 1) else Finset.Icc 1 k)).biUnion
      (fun ad => (chains k ad.1 false n).image (List.cons ad))

lemma mem_chains :
    ∀ (c : List (Fin q × ℕ)) (prev : Fin q) (first : Bool), ChainOK k prev first c →
      c ∈ chains k prev first c.length
  | [], _, _, _ => by simp [chains]
  | (a, d) :: rest, prev, first, h => by
    simp only [List.length_cons, chains]
    refine Finset.mem_biUnion.2 ⟨(a, d), ?_, Finset.mem_image.2
      ⟨rest, mem_chains rest a false h.2.2, rfl⟩⟩
    refine Finset.mem_product.2 ⟨by simpa using h.1, ?_⟩
    have h2 := h.2.1
    cases first <;> simp at h2 ⊢ <;> omega

lemma card_step (prev : Fin q) (first : Bool) (n B : ℕ)
    (hB : ∀ a : Fin q, (chains k a false n).card ≤ B) :
    (chains k prev first (n + 1)).card ≤ (q - 1) * (if first then k + 1 else k) * B := by
  rw [chains]
  refine (Finset.card_biUnion_le).trans ?_
  refine (Finset.sum_le_sum (fun ad _ => (Finset.card_image_le).trans (hB ad.1))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
  apply Nat.mul_le_mul_right
  have h1 : (Finset.univ.filter (fun a : Fin q => a ≠ prev)).card = q - 1 := by
    rw [Finset.filter_ne' Finset.univ prev, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [h1]
  cases first <;> simp

lemma card_chains_false (prev : Fin q) (n : ℕ) :
    (chains k prev false n).card ≤ ((q - 1) * k) ^ n := by
  induction n generalizing prev with
  | zero => simp [chains]
  | succ n ih =>
    refine (card_step prev false n _ ih).trans (le_of_eq ?_)
    simp only [Bool.false_eq_true, if_false]
    ring

/-! ### Labellings with prescribed values -/
lemma card_prescribed {α : Type*} [Fintype α] [DecidableEq α] {t : ℕ} (D : Finset α)
    (h : α → Fin t) (S : Finset (α → Fin t)) (hS : ∀ ℓ ∈ S, ∀ u ∈ D, ℓ u = h u) :
    S.card ≤ t ^ (Fintype.card α - D.card) := by
  have := Finset.card_le_card_of_injOn (fun ℓ : α → Fin t => fun u : ↥(Dᶜ) => ℓ u.1)
    (s := S) (t := (Finset.univ : Finset (↥(Dᶜ) → Fin t)))
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
  · refine this.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      Finset.card_compl]
  · intro ℓ1 h1 ℓ2 h2 heq
    funext u
    by_cases hu : u ∈ D
    · rw [hS ℓ1 h1 u hu, hS ℓ2 h2 u hu]
    · exact congrFun heq ⟨u, Finset.mem_compl.2 hu⟩

open Classical in
/-- Counting bound: few labellings make an active node `R`-bad. Needs girth `> 2R + 2`. -/
theorem card_bad_le {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (x : Fin m) (R : ℕ) (hR : 1 ≤ R) (hg : 2 * R + 2 < g) (a : Fin q) (s : Fin N) :
    (Finset.univ.filter (fun ℓ : Fin q × Fin N → Fin t =>
        active G f ℓ x a s ∧ ¬ Good G f ℓ x R a s)).card ≤
      (k + 1) * (q - 1) ^ R * k ^ (R - 1) * t ^ (q * N - (R + 1)) := by
  set T := t ^ (q * N - (R + 1)) with hT
  let L : List (Fin q × ℕ) → List (Fin q × Fin N) := fun c => (a, rep G a s) :: nodes G a s c
  let E : List (Fin q × ℕ) → Finset (Fin q × Fin N → Fin t) := fun c =>
    Finset.univ.filter (fun ℓ => ∀ u ∈ L c, ℓ u = f u.1 x)
  let C := (chains k a true R).filter (fun c => ChainOK k a true c ∧ c.length = R)
  have hsub : (Finset.univ.filter (fun ℓ : Fin q × Fin N → Fin t =>
      active G f ℓ x a s ∧ ¬ Good G f ℓ x R a s)) ⊆ C.biUnion E := by
    intro ℓ hℓ
    obtain ⟨hact, hng⟩ := (Finset.mem_filter.1 hℓ).2
    unfold Good at hng
    push Not at hng
    obtain ⟨c, hok, hca, hlen⟩ := hng
    have hok' := chainOK_take c a true R hok
    have hca' := chainActive_take G f ℓ x c a s R hca
    have hlen' : (c.take R).length = R := by simp; omega
    refine Finset.mem_biUnion.2 ⟨c.take R, Finset.mem_filter.2 ⟨?_, hok', hlen'⟩, ?_⟩
    · have := mem_chains (c.take R) a true hok'
      rwa [hlen'] at this
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hact
      · exact chainActive_nodes G f ℓ x a s _ hca' u hu
  have hE : ∀ c ∈ C, (E c).card ≤ T := by
    intro c hc
    obtain ⟨hok, hlen⟩ := (Finset.mem_filter.1 hc).2
    have hnd : (L c).Nodup := nodup_nodes G c a s true hok (by omega)
    have hD : (L c).toFinset.card = R + 1 := by
      rw [List.toFinset_card_of_nodup hnd]
      simp [L, length_nodes, hlen]
    have := card_prescribed (L c).toFinset (fun u => f u.1 x) (E c) (by
      intro ℓ hℓ u hu
      exact (Finset.mem_filter.1 hℓ).2 u (List.mem_toFinset.1 hu))
    rw [hD] at this
    simpa [Fintype.card_prod, Fintype.card_fin, hT] using this
  have hC : C.card ≤ (k + 1) * (q - 1) ^ R * k ^ (R - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
    refine (Finset.card_filter_le _ _).trans ?_
    refine (card_step a true n _ (fun b => card_chains_false b n)).trans (le_of_eq ?_)
    simp only [if_true, Nat.add_sub_cancel]
    ring
  calc _ ≤ (C.biUnion E).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ C, (E c).card := Finset.card_biUnion_le
    _ ≤ C.card * T := by
      have := Finset.sum_le_card_nsmul C (fun c => (E c).card) T hE
      simpa using this
    _ ≤ _ := Nat.mul_le_mul_right _ hC

end SubadditiveMMS580.Amplification.Dev.SS.PartB
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS
variable {q k g N : ℕ}
alias card_bad_le := SubadditiveMMS580.Amplification.Dev.SS.PartB.card_bad_le

end SubadditiveMMS580.Amplification.Dev.SS
end

section
set_option autoImplicit false
namespace SubadditiveMMS580.Amplification.Dev.SS.PartC
variable {q k g N : ℕ}
/-- The `σ a`-orbit of `s` (as a finset of seeds). -/
def orb (G : Guide q k g N) (a : Fin q) (s : Fin N) : Finset (Fin N) :=
  (Finset.range (k + 1)).image (fun e => (G.σ a ^ e) s)

lemma pow_mod_eq (G : Guide q k g N) (a : Fin q) (n : ℕ) :
    G.σ a ^ n = G.σ a ^ (n % (k + 1)) := by
  conv_lhs => rw [← Nat.div_add_mod n (k + 1), pow_add, pow_mul, G.pow_eq a, one_pow, one_mul]

lemma mem_orb (G : Guide q k g N) (a : Fin q) (s t : Fin N) :
    t ∈ orb G a s ↔ ∃ n : ℕ, (G.σ a ^ n) s = t := by
  unfold orb
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨e, -, he⟩
    exact ⟨e, he⟩
  · rintro ⟨n, hn⟩
    exact ⟨n % (k + 1), Nat.mod_lt _ (Nat.succ_pos _), by rw [← pow_mod_eq]; exact hn⟩

lemma self_mem_orb (G : Guide q k g N) (a : Fin q) (s : Fin N) : s ∈ orb G a s :=
  (mem_orb G a s s).2 ⟨0, by simp⟩

lemma orb_eq_of_mem (G : Guide q k g N) (a : Fin q) (s t : Fin N) (h : t ∈ orb G a s) :
    orb G a t = orb G a s := by
  obtain ⟨n, rfl⟩ := (mem_orb G a s t).1 h
  ext u
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m + n, by rw [pow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m + n * k, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    have : m + n * k + n = m + (k + 1) * n := by ring
    rw [this, pow_add, pow_mul, G.pow_eq, one_pow, mul_one]

lemma rep_eq_of_orb_eq (G : Guide q k g N) (a : Fin q) (s t : Fin N)
    (h : orb G a s = orb G a t) : rep G a s = rep G a t := by
  show (orb G a s).min' _ = (orb G a t).min' _
  congr 1

lemma active_of_orb_eq {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (a : Fin q) (s s' : Fin N)
    (h : orb G a s = orb G a s') (hs : active G f ℓ x a s) : active G f ℓ x a s' := by
  unfold active at *
  rw [← rep_eq_of_orb_eq G a s s' h]
  exact hs

lemma card_orb (G : Guide q k g N) (hg : 2 ≤ g) (a : Fin q) (s : Fin N) :
    (orb G a s).card = k + 1 := by
  unfold orb
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro e he e' he' h
  simp only [Finset.coe_range, Set.mem_Iio] at he he'
  dsimp only at h
  have key : ∀ e e' : ℕ, e < e' → e' < k + 1 → (G.σ a ^ e) s ≠ (G.σ a ^ e') s := by
    intro e e' hlt he' h
    apply G.girth [(a, e' - e)] (by simp) (by simp; omega)
      ⟨by simp; omega, by simp⟩ ((G.σ a ^ e) s)
    simp only [act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le]
    exact h.symm
  rcases lt_trichotomy e e' with hlt | heq | hlt
  · exact absurd h (key e e' hlt he')
  · exact heq
  · exact absurd h.symm (key e' e hlt he)

/-- Final (agent, seed) of a chain. -/
def lastN (G : Guide q k g N) : Fin q → Fin N → List (Fin q × ℕ) → Fin q × Fin N
  | a, p, [] => (a, p)
  | a, p, (b, d) :: rest => lastN G b ((G.σ a ^ d) p) rest

/-- Every node a chain visits lies in `Z`. -/
def InZ (G : Guide q k g N) (Z : Finset (Fin q × Finset (Fin N))) :
    Fin q → Fin N → List (Fin q × ℕ) → Prop
  | _, _, [] => True
  | a, p, (b, d) :: rest => (b, orb G b ((G.σ a ^ d) p)) ∈ Z ∧ InZ G Z b ((G.σ a ^ d) p) rest

lemma lastN_mem (G : Guide q k g N) (Z : Finset (Fin q × Finset (Fin N))) :
    ∀ (a : Fin q) (p : Fin N) (c : List (Fin q × ℕ)), (a, orb G a p) ∈ Z → InZ G Z a p c →
      ((lastN G a p c).1, orb G (lastN G a p c).1 (lastN G a p c).2) ∈ Z
  | _, _, [], h, _ => h
  | _, _, (b, _) :: rest, _, h => lastN_mem G Z b _ rest h.1 h.2

lemma append_step {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (Z : Finset (Fin q × Finset (Fin N))) :
    ∀ (a : Fin q) (p : Fin N) (first : Bool) (c : List (Fin q × ℕ)) (ay : Fin q) (py : Fin N)
      (b : Fin q) (d : ℕ),
    lastN G a p c = (ay, py) →
    ChainOK k a first c → ChainActive G f ℓ x a p c → InZ G Z a p c →
    b ≠ ay → 1 ≤ d → d ≤ k →
    active G f ℓ x b ((G.σ ay ^ d) py) →
    (b, orb G b ((G.σ ay ^ d) py)) ∈ Z →
    ChainOK k a first (c ++ [(b, d)]) ∧ ChainActive G f ℓ x a p (c ++ [(b, d)]) ∧
      InZ G Z a p (c ++ [(b, d)])
  | a, p, first, [], ay, py, b, d, hL, _, _, _, hb, hd1, hd2, hact, hZ => by
    simp only [lastN, Prod.mk.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    refine ⟨⟨hb, ?_, trivial⟩, ⟨hact, trivial⟩, ⟨hZ, trivial⟩⟩
    cases first <;> simp [hd1, hd2]
  | a, p, first, (b', d') :: rest, ay, py, b, d, hL, h1, h2, h3, hb, hd1, hd2, hact, hZ => by
    obtain ⟨ih1, ih2, ih3⟩ := append_step G f ℓ x Z b' _ false rest ay py b d hL h1.2.2 h2.2 h3.2
      hb hd1 hd2 hact hZ
    exact ⟨⟨h1.1, h1.2.1, ih1⟩, ⟨h2.1, ih2⟩, ⟨h3.1, ih3⟩⟩

/-- Hypothesis on a set of nodes: every node is the orbit of an active, good seed. -/
def NodesOK {m t : ℕ} (G : Guide q k g N) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (R : ℕ) (Z : Finset (Fin q × Finset (Fin N))) :
    Prop :=
  ∀ z ∈ Z, ∃ s, z.2 = orb G z.1 s ∧ active G f ℓ x z.1 s ∧ Good G f ℓ x R z.1 s

lemma exists_leaf {m t : ℕ} (G : Guide q k g N) (hg : 2 ≤ g) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (R : ℕ) (Z : Finset (Fin q × Finset (Fin N)))
    (hZ : NodesOK G f ℓ x R Z) (hne : Z.Nonempty) :
    ∃ y ∈ Z, ∃ P ⊆ y.2, k ≤ P.card ∧ ∀ s ∈ P, ∀ z ∈ Z, s ∈ z.2 → z = y := by
  by_contra hcon
  push Not at hcon
  have chains : ∀ n : ℕ, ∃ (a0 : Fin q) (s0 : Fin N) (c : List (Fin q × ℕ)),
      Good G f ℓ x R a0 s0 ∧ (a0, orb G a0 s0) ∈ Z ∧ ChainOK k a0 true c ∧
      ChainActive G f ℓ x a0 s0 c ∧ InZ G Z a0 s0 c ∧ c.length = n := by
    intro n
    induction n with
    | zero =>
      obtain ⟨z, hz⟩ := hne
      obtain ⟨s, hs, -, hgood⟩ := hZ z hz
      refine ⟨z.1, s, [], hgood, ?_, trivial, trivial, trivial, rfl⟩
      rw [← hs]
      exact hz
    | succ n ih =>
      obtain ⟨a0, s0, c, hgood, hz0, h1, h2, h3, hlen⟩ := ih
      have hy := lastN_mem G Z a0 s0 c hz0 h3
      rcases hL : lastN G a0 s0 c with ⟨ay, py⟩
      rw [hL] at hy
      obtain ⟨s', hs'P, z, hz, hs'z, hzy⟩ := hcon _ hy ((orb G ay py).erase py)
        (Finset.erase_subset _ _)
        (by rw [Finset.card_erase_of_mem (self_mem_orb G ay py), card_orb G hg]; simp)
      obtain ⟨hs'ne, hs'mem⟩ := Finset.mem_erase.1 hs'P
      have hs'mem' := hs'mem
      unfold orb at hs'mem'
      obtain ⟨d, hd, hds⟩ := Finset.mem_image.1 hs'mem'
      rw [Finset.mem_range] at hd
      obtain ⟨s'', hzs, hact, -⟩ := hZ z hz
      have hd0 : d ≠ 0 := by
        rintro rfl
        apply hs'ne
        rw [← hds]
        simp
      have horb : orb G z.1 s' = z.2 := by
        rw [hzs]
        exact orb_eq_of_mem G _ _ _ (hzs ▸ hs'z)
      have hb : z.1 ≠ ay := by
        intro hb
        apply hzy
        refine Prod.ext hb ?_
        rw [← horb, hb]
        exact orb_eq_of_mem G _ _ _ hs'mem
      have hact' : active G f ℓ x z.1 s' :=
        active_of_orb_eq G f ℓ x z.1 s'' s' (by rw [horb, hzs]) hact
      rw [← hds] at hact' horb
      obtain ⟨e1, e2, e3⟩ := append_step G f ℓ x Z a0 s0 true c ay py z.1 d hL h1 h2 h3 hb
        (by omega) (by omega) hact' (by rw [horb]; exact hz)
      exact ⟨a0, s0, c ++ [(z.1, d)], hgood, hz0, e1, e2, e3, by simp [hlen]⟩
  obtain ⟨a0, s0, c, hgood, -, h1, h2, -, hlen⟩ := chains R
  have := hgood c h1 h2
  omega

lemma main {m t : ℕ} (G : Guide q k g N) (hg : 2 ≤ g) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (R : ℕ) :
    ∀ n : ℕ, ∀ Z : Finset (Fin q × Finset (Fin N)), Z.card = n → NodesOK G f ℓ x R Z →
      ∃ give : Fin N → Option (Fin q), (∀ s a, give s = some a → (a, orb G a s) ∈ Z) ∧
        ∀ z ∈ Z, k ≤ (z.2.filter (fun s => give s = some z.1)).card := by
  intro n
  induction n with
  | zero =>
    intro Z hcard _
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    exact ⟨fun _ => none, by simp, by simp⟩
  | succ n ih =>
    intro Z hcard hZ
    have hne : Z.Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨y, hyZ, P, hPy, hPk, hPpriv⟩ := exists_leaf G hg f ℓ x R Z hZ hne
    obtain ⟨give, hg1, hg2⟩ := ih (Z.erase y) (by rw [Finset.card_erase_of_mem hyZ, hcard]; rfl)
      (fun z hz => hZ z (Finset.mem_of_mem_erase hz))
    classical
    refine ⟨fun s => if s ∈ P then some y.1 else give s, ?_, ?_⟩
    · intro s a h
      by_cases hs : s ∈ P
      · simp only [hs, if_true, Option.some.injEq] at h
        subst h
        obtain ⟨s0, hy2, -, -⟩ := hZ y hyZ
        have hsy : s ∈ orb G y.1 s0 := hy2 ▸ hPy hs
        rw [orb_eq_of_mem G _ _ _ hsy, ← hy2]
        exact hyZ
      · simp only [hs, if_false] at h
        exact Finset.mem_of_mem_erase (hg1 s a h)
    · intro z hz
      by_cases hzy : z = y
      · subst hzy
        refine hPk.trans (Finset.card_le_card ?_)
        intro s hs
        simp [hPy hs, hs]
      · refine (hg2 z (Finset.mem_erase.2 ⟨hzy, hz⟩)).trans (Finset.card_le_card ?_)
        intro s hs
        rw [Finset.mem_filter] at hs ⊢
        have hsP : s ∉ P := fun hsP => hzy (hPpriv s hsP z hz hs.1)
        simp only [hsP, if_false]
        exact hs

/-- Hall step: for each labelling and item, the seeds can hand the item out (each seed to at
most one active node through it) so that every good active node receives it at `k` of its
`k + 1` seeds. -/
theorem exists_give {m t : ℕ} (G : Guide q k g N) (hg : 2 ≤ g) (f : Fin q → Fin m → Fin t)
    (ℓ : Fin q × Fin N → Fin t) (x : Fin m) (R : ℕ) :
    ∃ give : Fin N → Option (Fin q),
      (∀ s a, give s = some a → active G f ℓ x a s) ∧
      ∀ a s, active G f ℓ x a s → Good G f ℓ x R a s →
        k ≤ ((Finset.range (k + 1)).filter (fun e => give ((G.σ a ^ e) s) = some a)).card := by
  classical
  let Y : Finset (Fin q × Finset (Fin N)) :=
    (Finset.univ.filter (fun p : Fin q × Fin N =>
      active G f ℓ x p.1 p.2 ∧ Good G f ℓ x R p.1 p.2)).image (fun p => (p.1, orb G p.1 p.2))
  have hY : NodesOK G f ℓ x R Y := by
    intro z hz
    obtain ⟨⟨a, s⟩, hmem, rfl⟩ := Finset.mem_image.1 hz
    rw [Finset.mem_filter] at hmem
    exact ⟨s, rfl, hmem.2.1, hmem.2.2⟩
  obtain ⟨give, h1, h2⟩ := main G hg f ℓ x R _ Y rfl hY
  refine ⟨give, ?_, ?_⟩
  · intro s a h
    obtain ⟨⟨a', s0⟩, hmem, heq⟩ := Finset.mem_image.1 (h1 s a h)
    rw [Finset.mem_filter] at hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, ho⟩ := heq
    exact active_of_orb_eq G f ℓ x a' s0 s ho hmem.2.1
  · intro a s hact hgood
    have hmem : (a, orb G a s) ∈ Y :=
      Finset.mem_image.2 ⟨(a, s), Finset.mem_filter.2 ⟨Finset.mem_univ _, hact, hgood⟩, rfl⟩
    refine (h2 _ hmem).trans ?_
    dsimp only
    unfold orb
    rw [Finset.filter_image]
    exact Finset.card_image_le

end SubadditiveMMS580.Amplification.Dev.SS.PartC
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS
variable {q k g N : ℕ}
alias exists_give := SubadditiveMMS580.Amplification.Dev.SS.PartC.exists_give

end SubadditiveMMS580.Amplification.Dev.SS
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification

end SubadditiveMMS580.Amplification
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS.PartD
open Finset
/-! ### Pure counting lemmas -/
/-- Rotating a seed by `σ ^ e` for each `e ≤ k` multiplies a count by `k + 1`. -/
theorem sum_orbit_count {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : ℕ) (P : Fin N → Prop)
    [DecidablePred P] :
    ∑ s : Fin N, ((range (k + 1)).filter (fun e => P ((σ ^ e) s))).card =
      (k + 1) * (univ.filter P).card := by
  simp_rw [card_filter]
  rw [Finset.sum_comm]
  have : ∀ e ∈ range (k + 1), (∑ s : Fin N, if P ((σ ^ e) s) then 1 else 0) =
      ∑ s : Fin N, if P s then 1 else 0 := fun e _ =>
    Equiv.sum_comp (σ ^ e) (fun s => if P s then 1 else 0)
  rw [Finset.sum_congr rfl this, sum_const, card_range, smul_eq_mul]

/-- Averaging: if the served counts dominate the good counts, and bad counts are small,
then some labelling and seed serve many agents. -/
theorem averaging {L S B : Type} [Fintype L] [Fintype S] [Fintype B]
    (served AG : L → B → S → Prop) [∀ ℓ b s, Decidable (served ℓ b s)]
    [∀ ℓ b s, Decidable (AG ℓ b s)] (k M : ℕ)
    (hval : ∀ ℓ b, k * (univ.filter (fun s => AG ℓ b s)).card ≤
      (k + 1) * (univ.filter (fun s => served ℓ b s)).card)
    (hbad : ∀ b, ∑ ℓ, (univ.filter (fun s => ¬ AG ℓ b s)).card ≤ M)
    (hsmall : k * Fintype.card B * M < Fintype.card L * Fintype.card S) :
    ∃ ℓ s, k * Fintype.card B ≤ (k + 1) * (univ.filter (fun b => served ℓ b s)).card := by
  by_contra hcon
  push Not at hcon
  set q := Fintype.card B
  set T := Fintype.card L
  set N := Fintype.card S
  set X := ∑ b, ∑ ℓ, (univ.filter (fun s => served ℓ b s)).card
  set Y := ∑ b, ∑ ℓ, (univ.filter (fun s => AG ℓ b s)).card
  set Z := ∑ b, ∑ ℓ, (univ.filter (fun s => ¬ AG ℓ b s)).card
  have hX : ∑ ℓ, ∑ s, (univ.filter (fun b => served ℓ b s)).card = X := by
    simp only [X, card_filter]
    calc (∑ ℓ : L, ∑ s : S, ∑ b : B, if served ℓ b s then 1 else 0)
        = ∑ ℓ : L, ∑ b : B, ∑ s : S, (if served ℓ b s then 1 else 0) :=
          Finset.sum_congr rfl (fun ℓ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have h1 : (k + 1) * X + T * N ≤ T * N * (k * q) := by
    rw [← hX, Finset.mul_sum]
    have : ∀ ℓ : L, (k + 1) * ∑ s, (univ.filter (fun b => served ℓ b s)).card + N ≤
        N * (k * q) := by
      intro ℓ
      rw [Finset.mul_sum]
      have h2 : ∑ s : S, ((k + 1) * (univ.filter (fun b => served ℓ b s)).card + 1) ≤
          ∑ _s : S, k * q := Finset.sum_le_sum (fun s _ => Nat.succ_le_of_lt (hcon ℓ s))
      rw [Finset.sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, sum_const,
        card_univ, smul_eq_mul] at h2
      exact h2
    have h3 := Finset.sum_le_sum (s := (univ : Finset L)) (fun ℓ _ => this ℓ)
    rw [Finset.sum_add_distrib, sum_const, card_univ, smul_eq_mul, sum_const, card_univ,
      smul_eq_mul] at h3
    calc _ = ∑ ℓ, (k + 1) * ∑ s, (univ.filter (fun b => served ℓ b s)).card + T * N := rfl
      _ ≤ T * (N * (k * q)) := h3
      _ = T * N * (k * q) := by ring
  have h2 : k * Y ≤ (k + 1) * X := by
    simp only [X, Y, Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun ℓ _ => hval ℓ b))
  have h3 : Y + Z = q * (T * N) := by
    simp only [Y, Z, ← Finset.sum_add_distrib, card_filter_add_card_filter_not, card_univ,
      sum_const, smul_eq_mul]
    rfl
  have h4 : Z ≤ q * M := by
    calc Z ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => hbad b)
      _ = q * M := by rw [sum_const, card_univ, smul_eq_mul]
  have h5 : k * Z ≤ k * (q * M) := Nat.mul_le_mul_left k h4
  have h6 : k * (q * (T * N)) = k * Y + k * Z := by rw [← h3, mul_add]
  have h7 : k * (q * (T * N)) = T * N * (k * q) := by ring
  have h8 : k * (q * M) = k * q * M := by ring
  omega

/-! ### The guide is large: alternating words have long orbits -/
/-- The alternating word `(a1 a0)^n`. -/
def altWord {q : ℕ} (a0 a1 : Fin q) : ℕ → List (Fin q × ℕ)
  | 0 => []
  | n + 1 => (a1, 1) :: (a0, 1) :: altWord a0 a1 n

theorem altWord_length {q : ℕ} (a0 a1 : Fin q) (n : ℕ) : (altWord a0 a1 n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [altWord, List.length_cons, ih]; ring

theorem altWord_snd {q : ℕ} (a0 a1 : Fin q) (n : ℕ) : ∀ p ∈ altWord a0 a1 n, p.2 = 1 := by
  induction n with
  | zero => simp [altWord]
  | succ n ih =>
    intro p hp
    simp only [altWord, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · rfl
    · rfl
    · exact ih p hp

theorem act_altWord {q N : ℕ} (σ : Fin q → Equiv.Perm (Fin N)) (a0 a1 : Fin q) (n : ℕ) :
    act σ (altWord a0 a1 n) = (σ a1 * σ a0) ^ n := by
  induction n with
  | zero => simp [altWord, act]
  | succ n ih =>
    simp only [act] at ih ⊢
    simp only [altWord, List.map_cons, List.prod_cons, ih, pow_one]
    rw [pow_succ', mul_assoc]

theorem chain_altWord {q : ℕ} (a0 a1 : Fin q) (h : a0 ≠ a1) (n : ℕ) :
    List.IsChain (fun p p' : Fin q × ℕ => p.1 ≠ p'.1) ((a0, 1) :: altWord a0 a1 n) := by
  induction n with
  | zero => exact List.IsChain.singleton _
  | succ n ih =>
    simp only [altWord]
    rw [List.isChain_cons_cons]
    refine ⟨h, ?_⟩
    rw [List.isChain_cons_cons]
    exact ⟨Ne.symm h, ih⟩

theorem reduced_altWord {q k : ℕ} (hk : 1 ≤ k) (a0 a1 : Fin q) (h : a0 ≠ a1) (n : ℕ) :
    Reduced q k (altWord a0 a1 n) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [altWord_snd a0 a1 n p hp]; exact ⟨le_rfl, hk⟩
  · cases n with
    | zero => exact List.IsChain.nil
    | succ n =>
      simp only [altWord]
      rw [List.isChain_cons_cons]
      exact ⟨Ne.symm h, chain_altWord a0 a1 h n⟩

theorem le_card_of_guide {q k g N : ℕ} (G : Guide q k g N) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (hN : 0 < N) (n0 : ℕ) (hn0 : 2 * n0 < g) : n0 + 1 ≤ N := by
  let a0 : Fin q := ⟨0, by omega⟩
  let a1 : Fin q := ⟨1, by omega⟩
  have ha : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  let τ := G.σ a1 * G.σ a0
  have hfix : ∀ n, 1 ≤ n → n ≤ n0 → ∀ s, (τ ^ n) s ≠ s := by
    intro n hn1 hn s
    have := G.girth (altWord a0 a1 n) (by
        intro h0; have := congrArg List.length h0
        rw [altWord_length] at this; simp at this; omega)
      (by rw [altWord_length]; omega) (reduced_altWord hk a0 a1 ha n) s
    rwa [act_altWord] at this
  let s0 : Fin N := ⟨0, hN⟩
  have hne : ∀ i j : ℕ, i < j → j ≤ n0 → (τ ^ j) s0 ≠ (τ ^ i) s0 := by
    intro i j hij hj heq
    have hsplit : τ ^ j = τ ^ (j - i) * τ ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [hsplit, Equiv.Perm.mul_apply] at heq
    exact hfix (j - i) (by omega) (by omega) _ heq
  have hinj : Function.Injective (fun i : Fin (n0 + 1) => (τ ^ (i : ℕ)) s0) := by
    intro i j hij
    simp only at hij
    by_contra hc
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hc) with h | h
    · exact hne i j h (by omega) hij.symm
    · exact hne j i h (by omega) hij
  simpa using Fintype.card_le_of_injective _ hinj

/-! ### Choice of the radius `R` -/
theorem exists_R (q k m : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) :
    ∃ R, 1 ≤ R ∧ m * (k + 1) * (q - 1) ^ R < k * q ^ R := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set r : ℝ := ((q : ℝ) - 1) / q
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hy : (0 : ℝ) < k / (m * (k + 1) + 1) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hy hr1
  refine ⟨n + 1, by omega, ?_⟩
  have h1 : r ^ (n + 1) < k / (m * (k + 1) + 1) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)) hn
  have hqpos : (0 : ℝ) < (q : ℝ) ^ (n + 1) := by positivity
  rw [div_pow, div_lt_div_iff₀ hqpos (by positivity)] at h1
  have hcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h2 : ((m * (k + 1) * (q - 1) ^ (n + 1) : ℕ) : ℝ) < ((k * q ^ (n + 1) : ℕ) : ℝ) := by
    push_cast
    rw [hcast]
    have : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ (n + 1) := by
      apply pow_nonneg; linarith
    nlinarith
  exact_mod_cast h2

theorem bound_small (q k m t R N : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) (ht : k * q ≤ t) (hR : 1 ≤ R)
    (hR' : q = 1 ∨ (m * (k + 1) * (q - 1) ^ R < k * q ^ R ∧ R + 1 ≤ q * N)) :
    k * q * m * ((k + 1) * (q - 1) ^ R * k ^ (R - 1) * t ^ (q * N - (R + 1))) < t ^ (q * N) := by
  have ht1 : 1 ≤ t := le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) ht
  rcases hR' with h1 | ⟨hmain, hqN⟩
  · subst h1
    simp only [Nat.sub_self, zero_pow (by omega : R ≠ 0), mul_zero, zero_mul]
    positivity
  · obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    set P := t ^ (q * N - (R' + 1 + 1))
    have hP : 0 < P := by positivity
    have hsplit : t ^ (q * N) = t ^ (R' + 1 + 1) * P := by
      rw [← pow_add, Nat.add_sub_cancel' hqN]
    rw [hsplit]
    have hK : 0 < k * q * k ^ R' := by positivity
    have e1 : k * q * m * ((k + 1) * (q - 1) ^ (R' + 1) * k ^ (R' + 1 - 1) * P) =
        (k * q * k ^ R') * (m * (k + 1) * (q - 1) ^ (R' + 1)) * P := by
      simp only [Nat.add_sub_cancel]; ring
    have e2 : (k * q * k ^ R') * (k * q ^ (R' + 1)) = (k * q) ^ (R' + 1 + 1) := by ring
    rw [e1]
    calc (k * q * k ^ R') * (m * (k + 1) * (q - 1) ^ (R' + 1)) * P
        < (k * q * k ^ R') * (k * q ^ (R' + 1)) * P := by
          apply Nat.mul_lt_mul_of_pos_right _ hP
          exact Nat.mul_lt_mul_of_pos_left hmain hK
      _ = (k * q) ^ (R' + 1 + 1) * P := by rw [e2]
      _ ≤ t ^ (R' + 1 + 1) * P := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ht _)

end SubadditiveMMS580.Amplification.Dev.SS.PartD
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification.Dev.SS.PartD
open Finset
open Classical
variable {q k g N m t : ℕ} (G : Guide q k g N) (hg : 2 ≤ g) (f : Fin q → Fin m → Fin t)
  (R : ℕ)
/-! ### Bundles from the Hall step -/
/-- The chosen handing-out map for item `x`. -/
noncomputable def give (ℓ : Fin q × Fin N → Fin t) (x : Fin m) : Fin N → Option (Fin q) :=
  Classical.choose (exists_give G hg f ℓ x R)

theorem give_spec (ℓ : Fin q × Fin N → Fin t) (x : Fin m) :
    (∀ s a, give G hg f R ℓ x s = some a → active G f ℓ x a s) ∧
      ∀ a s, active G f ℓ x a s → Good G f ℓ x R a s →
        k ≤ ((range (k + 1)).filter
          (fun e => give G hg f R ℓ x ((G.σ a ^ e) s) = some a)).card :=
  Classical.choose_spec (exists_give G hg f ℓ x R)

/-- The bundle agent `b` gets at seed `s`. -/
noncomputable def bundle (ℓ : Fin q × Fin N → Fin t) (b : Fin q) (s : Fin N) :
    Finset (Fin m) :=
  univ.filter (fun x => give G hg f R ℓ x s = some b)

/-- Every item of the node `(b, s)` is good. -/
def AllGood (ℓ : Fin q × Fin N → Fin t) (b : Fin q) (s : Fin N) : Prop :=
  ∀ x, active G f ℓ x b s → Good G f ℓ x R b s

theorem served_many (w : Fin q → Finset (Fin m) → ℝ) (hmono : ∀ b, IsMonotone (w b))
    (hsub : ∀ b, SubmodOrder.Subadditive (w b))
    (hpart : ∀ b j, 1 ≤ w b (univ.filter (fun x => f b x = j)))
    (ℓ : Fin q × Fin N → Fin t) (b : Fin q) (s0 : Fin N) (hAG : AllGood G f R ℓ b s0) :
    k ≤ ((range (k + 1)).filter
      (fun e => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b ((G.σ b ^ e) s0)))).card := by
  by_contra hlt
  push Not at hlt
  have hU : 1 < ((range (k + 1)).filter
      (fun e => ¬ ((1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b ((G.σ b ^ e) s0))))).card := by
    have := card_filter_add_card_filter_not
      (s := range (k + 1)) (fun e => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b ((G.σ b ^ e) s0)))
    rw [card_range] at this
    omega
  obtain ⟨e, he, e', he', hee'⟩ := Finset.one_lt_card.mp hU
  simp only [mem_filter, mem_range, not_le] at he he'
  set L := univ.filter (fun x => f b x = ℓ (b, rep G b s0))
  have hL : L ⊆ bundle G hg f R ℓ b ((G.σ b ^ e) s0) ∪ bundle G hg f R ℓ b ((G.σ b ^ e') s0) := by
    intro x hx
    simp only [L, mem_filter, mem_univ, true_and] at hx
    have hact : active G f ℓ x b s0 := hx.symm
    have hcnt := (give_spec G hg f R ℓ x).2 b s0 hact (hAG x hact)
    have hneg := card_filter_add_card_filter_not (s := range (k + 1))
      (fun e => give G hg f R ℓ x ((G.σ b ^ e) s0) = some b)
    rw [card_range] at hneg
    by_contra hnot
    simp only [bundle, mem_union, mem_filter, mem_univ, true_and, not_or] at hnot
    have h2 : 1 < ((range (k + 1)).filter
        (fun e => ¬ give G hg f R ℓ x ((G.σ b ^ e) s0) = some b)).card :=
      Finset.one_lt_card.mpr ⟨e, by simp [he.1, hnot.1], e', by simp [he'.1, hnot.2], hee'⟩
    omega
  have h1 := hpart b (ℓ (b, rep G b s0))
  have h2 := hmono b _ _ hL
  have h3 := hsub b (bundle G hg f R ℓ b ((G.σ b ^ e) s0)) (bundle G hg f R ℓ b ((G.σ b ^ e') s0))
  linarith [he.2, he'.2]

theorem val_bound (w : Fin q → Finset (Fin m) → ℝ) (hmono : ∀ b, IsMonotone (w b))
    (hsub : ∀ b, SubmodOrder.Subadditive (w b))
    (hpart : ∀ b j, 1 ≤ w b (univ.filter (fun x => f b x = j)))
    (ℓ : Fin q × Fin N → Fin t) (b : Fin q) :
    k * (univ.filter (fun s => AllGood G f R ℓ b s)).card ≤
      (k + 1) * (univ.filter (fun s => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b s))).card := by
  rw [← sum_orbit_count (G.σ b) k (fun s => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b s))]
  calc k * (univ.filter (fun s => AllGood G f R ℓ b s)).card
      = ∑ _s ∈ univ.filter (fun s => AllGood G f R ℓ b s), k := by
        rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ s ∈ univ.filter (fun s => AllGood G f R ℓ b s), ((range (k + 1)).filter
          (fun e => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b ((G.σ b ^ e) s)))).card := by
        apply Finset.sum_le_sum
        intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs
        exact served_many G hg f R w hmono hsub hpart ℓ b s hs
    _ ≤ _ := Finset.sum_le_sum_of_subset (filter_subset _ _)

theorem sum_card_filter_swap {α β : Type} [Fintype α] [Fintype β] (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    ∑ a, (univ.filter (fun b => P a b)).card = ∑ b, (univ.filter (fun a => P a b)).card := by
  simp only [card_filter]
  exact Finset.sum_comm

theorem bad_bound (hR : 1 ≤ R) (hgR : 2 * R + 2 < g) (b : Fin q) :
    ∑ ℓ : Fin q × Fin N → Fin t, (univ.filter (fun s => ¬ AllGood G f R ℓ b s)).card ≤
      m * (N * ((k + 1) * (q - 1) ^ R * k ^ (R - 1) * t ^ (q * N - (R + 1)))) := by
  have h1 : ∀ ℓ : Fin q × Fin N → Fin t,
      (univ.filter (fun s => ¬ AllGood G f R ℓ b s)).card ≤
        ∑ x : Fin m, (univ.filter
          (fun s => active G f ℓ x b s ∧ ¬ Good G f ℓ x R b s)).card := by
    intro ℓ
    refine le_trans (card_le_card ?_) (card_biUnion_le (s := univ) (t := fun x => univ.filter
          (fun s => active G f ℓ x b s ∧ ¬ Good G f ℓ x R b s)))
    intro s hs
    simp only [AllGood, mem_filter, mem_univ, true_and, not_forall] at hs
    obtain ⟨x, hx1, hx2⟩ := hs
    simp only [mem_biUnion, mem_univ, mem_filter, true_and]
    exact ⟨x, hx1, hx2⟩
  calc _ ≤ ∑ ℓ : Fin q × Fin N → Fin t, ∑ x : Fin m, (univ.filter
          (fun s => active G f ℓ x b s ∧ ¬ Good G f ℓ x R b s)).card :=
        Finset.sum_le_sum (fun ℓ _ => h1 ℓ)
    _ = ∑ x : Fin m, ∑ s : Fin N, (univ.filter
          (fun ℓ : Fin q × Fin N → Fin t =>
            active G f ℓ x b s ∧ ¬ Good G f ℓ x R b s)).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact sum_card_filter_swap (fun ℓ s => active G f ℓ x b s ∧ ¬ Good G f ℓ x R b s)
    _ ≤ ∑ _x : Fin m, ∑ _s : Fin N,
          (k + 1) * (q - 1) ^ R * k ^ (R - 1) * t ^ (q * N - (R + 1)) := by
        refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun s _ => ?_))
        exact card_bad_le G f x R hR hgR b s
    _ = _ := by simp [sum_const, card_univ]

end SubadditiveMMS580.Amplification.Dev.SS.PartD
end

section
set_option autoImplicit false
open MultiAllocToAlloc.Subadditive
namespace SubadditiveMMS580.Amplification
open Finset Dev.SS Dev.SS.PartD
theorem chk_lemma_3_2 (t : ℕ) {m : ℕ} (v : Fin t → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (hmms : ∀ i, LittleCharity.MMS.mms (v i) t Finset.univ = 1)
    (Q : Finset (Fin t)) (hQ : Q.Nonempty) :
    ∃ A : Fin t → Finset (Fin m), IsAllocation A ∧
      ((t / Q.card : ℕ) : ℝ) * (Q.card : ℝ) / (((t / Q.card : ℕ) : ℝ) + 1) ≤
        ((Q.filter (fun i => (1 : ℝ) / 2 ≤ v i (A i))).card : ℝ) := by
  classical
  set q := Q.card with hqdef
  have hq1 : 1 ≤ q := Finset.card_pos.mpr hQ
  have hqt : q ≤ t := by
    simpa using Finset.card_le_univ Q
  set k := t / q with hkdef
  have hk : 1 ≤ k := Nat.div_pos hqt (by omega)
  have hkt : k * q ≤ t := Nat.div_mul_le_self t q
  have ht0 : 0 < t := by omega
  -- MMS partitions
  have hF : ∀ i, ∃ φ : Fin m → Fin t, ∀ j, 1 ≤ v i (univ.filter (fun x => φ x = j)) := by
    intro i
    have : Nonempty (Fin t) := ⟨⟨0, ht0⟩⟩
    obtain ⟨φ, hφ⟩ := exists_eq_ciSup_of_finite
      (f := fun φ : Fin m → Fin t => ⨅ j : Fin t, v i (univ.filter (fun x => φ x = j)))
    refine ⟨φ, fun j => ?_⟩
    have h1 : (1 : ℝ) = ⨅ j : Fin t, v i (univ.filter (fun x => φ x = j)) := by
      rw [hφ, ← hmms i]
      unfold LittleCharity.MMS.mms
      congr 1
    rw [h1]
    exact ciInf_le (Finite.bddBelow_range _) j
  choose F hFspec using hF
  let ag : Fin q → Fin t := fun b => (Q.equivFin.symm b : Fin t)
  have hagQ : ∀ b, ag b ∈ Q := fun b => (Q.equivFin.symm b).2
  have hagEq : ∀ b, Q.equivFin ⟨ag b, hagQ b⟩ = b := fun b => by
    simp [ag]
  let f : Fin q → Fin m → Fin t := fun b => F (ag b)
  let w : Fin q → Finset (Fin m) → ℝ := fun b => v (ag b)
  -- the radius
  obtain ⟨R, hR1, hRq⟩ : ∃ R, 1 ≤ R ∧ (q = 1 ∨ m * (k + 1) * (q - 1) ^ R < k * q ^ R) := by
    by_cases h : q = 1
    · exact ⟨1, le_rfl, Or.inl h⟩
    · obtain ⟨R, h1, h2⟩ := exists_R q k m (by omega) hk
      exact ⟨R, h1, Or.inr h2⟩
  obtain ⟨N, hN, ⟨G⟩⟩ := exists_guide q k (2 * R + 3) hk
  have hg : 2 ≤ 2 * R + 3 := by omega
  have hR' : q = 1 ∨ (m * (k + 1) * (q - 1) ^ R < k * q ^ R ∧ R + 1 ≤ q * N) := by
    rcases hRq with h | h
    · exact Or.inl h
    · by_cases hq1' : q = 1
      · exact Or.inl hq1'
      · refine Or.inr ⟨h, ?_⟩
        have := le_card_of_guide G (by omega) hk hN (R + 1) (by omega)
        nlinarith
  set B0 := (k + 1) * (q - 1) ^ R * k ^ (R - 1) * t ^ (q * N - (R + 1))
  have hsmall0 := bound_small q k m t R N hk hq1 hkt hR1 hR'
  obtain ⟨ℓ, s, hcount⟩ := averaging
    (L := Fin q × Fin N → Fin t) (S := Fin N) (B := Fin q)
    (fun ℓ b s => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b s))
    (fun ℓ b s => AllGood G f R ℓ b s) k (m * (N * B0))
    (fun ℓ b => val_bound G hg f R w (fun b => hmono (ag b)) (fun b => hsub (ag b))
      (fun b j => hFspec (ag b) j) ℓ b)
    (fun b => bad_bound G f R hR1 (by omega) b)
    (by
      simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_prod]
      have : k * q * (m * (N * B0)) = (k * q * m * B0) * N := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_right hsmall0 hN)
  simp only [Fintype.card_fin] at hcount
  let A : Fin t → Finset (Fin m) := fun i =>
    if h : i ∈ Q then bundle G hg f R ℓ (Q.equivFin ⟨i, h⟩) s else ∅
  have hAag : ∀ b, A (ag b) = bundle G hg f R ℓ b s := fun b => by
    simp only [A, dif_pos (hagQ b), hagEq b]
  refine ⟨A, ?_, ?_⟩
  · intro i j hij
    simp only [A]
    split_ifs with hi hj
    · rw [Finset.disjoint_left]
      intro x hxi hxj
      simp only [bundle, mem_filter, mem_univ, true_and] at hxi hxj
      rw [hxi] at hxj
      have := Q.equivFin.injective (Option.some_injective _ hxj)
      exact hij (congrArg Subtype.val this)
    · exact Finset.disjoint_empty_right _
    · exact Finset.disjoint_empty_left _
    · exact Finset.disjoint_empty_left _
  · have hcard : (Q.filter (fun i => (1 : ℝ) / 2 ≤ v i (A i))).card =
        (univ.filter (fun b => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b s))).card := by
      symm
      refine Finset.card_bij (fun b _ => ag b) ?_ ?_ ?_
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb
        simp only [mem_filter]
        exact ⟨hagQ b, by rw [hAag b]; exact hb⟩
      · intro b _ b' _ hbb'
        have : Q.equivFin.symm b = Q.equivFin.symm b' := Subtype.ext hbb'
        exact Q.equivFin.symm.injective this
      · intro i hi
        simp only [mem_filter] at hi
        refine ⟨Q.equivFin ⟨i, hi.1⟩, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          have : ag (Q.equivFin ⟨i, hi.1⟩) = i := by simp [ag]
          have h2 := hi.2
          rw [← this] at h2
          rw [hAag] at h2
          simpa [w, this] using h2
        · simp [ag]
    rw [hcard]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hk1]
    have : ((k * q : ℕ) : ℝ) ≤ (((k + 1) * (univ.filter
        (fun b => (1 : ℝ) / 2 ≤ w b (bundle G hg f R ℓ b s))).card : ℕ) : ℝ) := by
      exact_mod_cast hcount
    push_cast at this
    linarith

end SubadditiveMMS580.Amplification
end


theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_lemma_3_2 := @SubadditiveMMS580.Amplification.chk_lemma_3_2
