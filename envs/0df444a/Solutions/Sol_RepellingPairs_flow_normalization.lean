-- Prove2me | solution 1 for RepellingPairs.flow_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:48:14.525899+00:00
-- url     : https://prove2.me/submissions/70884c76-7541-46ab-ba76-ce844a52faf3

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_Repel
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_IntegralFlow
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_RealFlow
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.FlowNormRat

open Finset

/-- Rational approximation: a real solution of a homogeneous rational system of inequalities with a
real objective yields a rational one. -/
theorem exists_rat_solution {ν ε : Type*} [Fintype ν] [Fintype ε] (A : ε → ν → ℤ) (c : ν → ℝ)
    (z : ν → ℝ) (hz : ∀ v, 0 ≤ z v) (hA : ∀ e, ∑ v, (A e v : ℝ) * z v ≤ 0)
    (hc : 0 < ∑ v, c v * z v) :
    ∃ w : ν → ℚ, (∀ v, 0 ≤ w v) ∧ (∀ e, ∑ v, (A e v : ℚ) * w v ≤ 0) ∧
      0 < ∑ v, c v * (w v : ℝ) := by
  classical
  -- ℚ-basis of the span of the coordinates
  let L : Submodule ℚ ℝ := Submodule.span ℚ (Set.range z)
  have : FiniteDimensional ℚ L := FiniteDimensional.span_of_finite ℚ (Set.finite_range z)
  let d := Module.finrank ℚ L
  let b : Module.Basis (Fin d) ℚ L := Module.finBasis ℚ L
  have hzL : ∀ v, z v ∈ L := fun v => Submodule.subset_span ⟨v, rfl⟩
  let u : Fin d → ν → ℚ := fun s v => b.repr ⟨z v, hzL v⟩ s
  let β : Fin d → ℝ := fun s => ((b s : L) : ℝ)
  have hzu : ∀ v, z v = ∑ s, (u s v : ℝ) * β s := by
    intro v
    have h := b.sum_repr ⟨z v, hzL v⟩
    have h2 := congrArg (fun x : L => (x : ℝ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    simp only [u, β]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Rat.smul_def]
  have hβ : LinearIndependent ℚ β := by
    have := b.linearIndependent.map' L.subtype (by simp)
    exact this
  -- a rational form vanishing at z vanishes on every u s
  have hform : ∀ a : ν → ℚ, ∑ v, (a v : ℝ) * z v = 0 → ∀ s, ∑ v, a v * u s v = 0 := by
    intro a ha
    have h1 : ∑ s, (∑ v, a v * u s v : ℚ) • β s = 0 := by
      have : ∑ s, (∑ v, a v * u s v : ℚ) • β s = ∑ v, (a v : ℝ) * z v := by
        simp_rw [Rat.smul_def, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hzu v, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      rw [this, ha]
    exact Fintype.linearIndependent_iff.mp hβ _ h1
  let W : (Fin d → ℚ) → ν → ℚ := fun b' v => ∑ s, b' s * u s v
  let Wr : (Fin d → ℝ) → ν → ℝ := fun b' v => ∑ s, b' s * (u s v : ℝ)
  have hWr_cont : ∀ v, Continuous fun b' : Fin d → ℝ => Wr b' v := fun v => by
    unfold Wr; fun_prop
  have hWrβ : Wr β = z := by
    funext v; simp only [Wr]; rw [hzu v]; exact Finset.sum_congr rfl fun s _ => by ring
  -- open neighbourhood
  let U : Set (Fin d → ℝ) :=
    {b' | (∀ v, z v ≠ 0 → 0 < Wr b' v) ∧
      (∀ e, ∑ v, (A e v : ℝ) * z v ≠ 0 → ∑ v, (A e v : ℝ) * Wr b' v < 0) ∧
      0 < ∑ v, c v * Wr b' v}
  have hβU : U ∈ nhds β := by
    have e1 : ∀ᶠ b' in nhds β, ∀ v, z v ≠ 0 → 0 < Wr b' v := by
      rw [Filter.eventually_all]
      intro v
      by_cases hv : z v ≠ 0
      · have h0 : 0 < Wr β v := by rw [hWrβ]; exact lt_of_le_of_ne (hz v) (Ne.symm hv)
        exact ((continuousAt_const).eventually_lt (hWr_cont v).continuousAt h0).mono
          fun b' hb _ => hb
      · exact Filter.Eventually.of_forall fun b' h => absurd h hv
    have e2 : ∀ᶠ b' in nhds β, ∀ e, ∑ v, (A e v : ℝ) * z v ≠ 0 →
        ∑ v, (A e v : ℝ) * Wr b' v < 0 := by
      rw [Filter.eventually_all]
      intro e
      by_cases hv : ∑ v, (A e v : ℝ) * z v ≠ 0
      · have h0 : ∑ v, (A e v : ℝ) * Wr β v < 0 := by
          rw [hWrβ]; exact lt_of_le_of_ne (hA e) hv
        have hc2 : Continuous fun b' : Fin d → ℝ => ∑ v, (A e v : ℝ) * Wr b' v :=
          continuous_finsetSum _ fun v _ => continuous_const.mul (hWr_cont v)
        exact (hc2.continuousAt.eventually_lt (continuousAt_const) h0).mono
          fun b' hb _ => hb
      · exact Filter.Eventually.of_forall fun b' h => absurd h hv
    have e3 : ∀ᶠ b' in nhds β, 0 < ∑ v, c v * Wr b' v := by
      have h0 : 0 < ∑ v, c v * Wr β v := by rw [hWrβ]; exact hc
      have hc2 : Continuous fun b' : Fin d → ℝ => ∑ v, c v * Wr b' v :=
        continuous_finsetSum _ fun v _ => continuous_const.mul (hWr_cont v)
      exact (continuousAt_const).eventually_lt hc2.continuousAt h0
    exact (e1.and (e2.and e3))
  obtain ⟨b', hb'⟩ : ∃ b' : Fin d → ℚ, (fun s => (b' s : ℝ)) ∈ U := by
    have hd : DenseRange (fun b' : Fin d → ℚ => fun s => (b' s : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    obtain ⟨x, hx, ⟨y, hy⟩⟩ := mem_closure_iff_nhds.mp (hd β) U hβU
    exact ⟨y, by rw [← hy] at hx; exact hx⟩
  have hWcast : ∀ v, ((W b' v : ℚ) : ℝ) = Wr (fun s => (b' s : ℝ)) v := by
    intro v; simp [W, Wr]
  refine ⟨W b', ?_, ?_, ?_⟩
  · intro v
    by_cases hv : z v = 0
    · have := hform (fun v' => if v' = v then 1 else 0)
        (by rw [Finset.sum_eq_single v (fun v' _ hv' => by simp [hv']) (by simp)]; simp [hv])
      have h0 : ∀ s, u s v = 0 := fun s => by simpa using this s
      simp [W, h0]
    · have := hb'.1 v hv
      rw [← hWcast] at this
      exact_mod_cast this.le
  · intro e
    by_cases he : ∑ v, (A e v : ℝ) * z v = 0
    · have := hform (fun v => (A e v : ℚ)) (by simpa using he)
      have h0 : ∑ v, (A e v : ℚ) * W b' v = 0 := by
        simp only [W, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun s _ => ?_
        have h := this s
        calc ∑ v, (A e v : ℚ) * (b' s * u s v) = b' s * ∑ v, (A e v : ℚ) * u s v := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
          _ = 0 := by rw [h, mul_zero]
      exact h0.le
    · have := hb'.2.1 e he
      have h3 : ((∑ v, (A e v : ℚ) * W b' v : ℚ) : ℝ) < 0 := by
        simpa [hWcast] using this
      exact_mod_cast h3.le
  · have := hb'.2.2
    simpa [hWcast] using this

/-- Integral version: a real solution gives a natural-number one. -/
theorem exists_nat_solution {ν ε : Type*} [Fintype ν] [Fintype ε] (A : ε → ν → ℤ) (c : ν → ℝ)
    (z : ν → ℝ) (hz : ∀ v, 0 ≤ z v) (hA : ∀ e, ∑ v, (A e v : ℝ) * z v ≤ 0)
    (hc : 0 < ∑ v, c v * z v) :
    ∃ n : ν → ℕ, (∀ e, ∑ v, (A e v : ℝ) * (n v : ℝ) ≤ 0) ∧ 0 < ∑ v, c v * (n v : ℝ) := by
  classical
  obtain ⟨w, hw0, hwA, hwc⟩ := exists_rat_solution A c z hz hA hc
  let N : ℕ := ∏ v, (w v).den
  have hNpos : 0 < N := Finset.prod_pos fun v _ => (w v).den_pos
  have hint : ∀ v, ∃ m : ℤ, (w v) * (N : ℚ) = m := by
    intro v
    have hdvd : (w v).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
    obtain ⟨r, hr⟩ := hdvd
    refine ⟨(w v).num * r, ?_⟩
    have := Rat.mul_den_eq_num (w v)
    rw [hr]; push_cast
    rw [← this]; ring
  choose m hm using hint
  have hm0 : ∀ v, 0 ≤ m v := by
    intro v
    have : (0 : ℚ) ≤ (m v : ℚ) := by rw [← hm v]; exact mul_nonneg (hw0 v) (by positivity)
    exact_mod_cast this
  refine ⟨fun v => (m v).toNat, ?_, ?_⟩
  · intro e
    have key : ∀ v, (((m v).toNat : ℕ) : ℝ) = (N : ℝ) * ((w v : ℚ) : ℝ) := by
      intro v
      have h1 : (((m v).toNat : ℕ) : ℤ) = m v := Int.toNat_of_nonneg (hm0 v)
      have h2 : (((m v).toNat : ℕ) : ℚ) = (w v) * N := by
        have : ((((m v).toNat : ℕ) : ℤ) : ℚ) = (m v : ℚ) := by rw [h1]
        rw [hm v] at *; exact_mod_cast this
      have h3 : ((((m v).toNat : ℕ) : ℚ) : ℝ) = (((w v) * N : ℚ) : ℝ) := by rw [h2]
      push_cast at h3
      rw [h3]; ring
    simp_rw [key]
    have : ∑ v, (A e v : ℝ) * ((N : ℝ) * (w v : ℝ)) = (N : ℝ) * ((∑ v, (A e v : ℚ) * w v : ℚ) : ℝ) := by
      push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [this]
    have h := hwA e
    have : ((∑ v, (A e v : ℚ) * w v : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  · have key : ∀ v, (((m v).toNat : ℕ) : ℝ) = (N : ℝ) * ((w v : ℚ) : ℝ) := by
      intro v
      have h1 : (((m v).toNat : ℕ) : ℤ) = m v := Int.toNat_of_nonneg (hm0 v)
      have h2 : (((m v).toNat : ℕ) : ℚ) = (w v) * N := by
        have : ((((m v).toNat : ℕ) : ℤ) : ℚ) = (m v : ℚ) := by rw [h1]
        rw [hm v] at *; exact_mod_cast this
      have h3 : ((((m v).toNat : ℕ) : ℚ) : ℝ) = (((w v) * N : ℚ) : ℝ) := by rw [h2]
      push_cast at h3
      rw [h3]; ring
    simp_rw [key]
    have : ∑ v, c v * ((N : ℝ) * (w v : ℝ)) = (N : ℝ) * ∑ v, c v * (w v : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [this]
    exact mul_pos (by exact_mod_cast hNpos) hwc

end RepellingPairs.Dev.FlowNormRat
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.FlowNormWalk

open RepellingPairs


variable {V : Type u} {E : Type v} {G : Multigraph V E}

open Multigraph in
theorem edges_append {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil v => simp [Walk.append, Walk.edges]
  | cons e h p ih => simp [Walk.append, Walk.edges, ih]

open Multigraph in
theorem edges_reverse {u w : V} (p : G.Walk u w) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil v => simp [Walk.reverse, Walk.edges]
  | cons e h p ih => simp [Walk.reverse, Walk.edges, edges_append, ih]

open Multigraph in
theorem support_ne_nil {u w : V} (p : G.Walk u w) : p.support ≠ [] := by
  cases p <;> simp [Walk.support]

open Multigraph in
theorem support_append {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p with
  | nil v => simp [Walk.append, Walk.support]
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, ih]
    have := support_ne_nil p
    rw [List.dropLast_cons_of_ne_nil this]; rfl

open Multigraph in
theorem start_mem {u w : V} (p : G.Walk u w) : u ∈ p.support := by
  cases p <;> simp [Walk.support]

open Multigraph in
theorem end_mem {u w : V} (p : G.Walk u w) : w ∈ p.support := by
  induction p with
  | nil v => simp [Walk.support]
  | cons e h p ih => simp [Walk.support, ih]

open Multigraph in
theorem mem_append_right {u w x : V} (p : G.Walk u w) (q : G.Walk w x) {y : V}
    (hy : y ∈ q.support) : y ∈ (p.append q).support := by
  rw [support_append]; exact List.mem_append_right _ hy

open Multigraph in
theorem mem_append_left {u w x : V} (p : G.Walk u w) (q : G.Walk w x) {y : V}
    (hy : y ∈ p.support) : y ∈ (p.append q).support := by
  induction p with
  | nil v =>
    simp only [Walk.support, List.mem_singleton] at hy
    subst hy; simpa [Walk.append] using start_mem q
  | cons e h p ih =>
    simp only [Walk.append, Walk.support, List.mem_cons] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (ih q hy)

open Multigraph in
theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons e h p ih => simp [Walk.append, ih]

open Multigraph in
theorem support_reverse {u w : V} (p : G.Walk u w) : p.reverse.support = p.support.reverse := by
  induction p with
  | nil v => simp [Walk.reverse, Walk.support]
  | cons e h p ih =>
    rename_i u' v' w'
    simp only [Walk.reverse, support_append, ih, Walk.support]
    obtain ⟨tl, htl⟩ : ∃ tl, p.support = v' :: tl := by cases p <;> simp [Walk.support]
    rw [htl]
    simp

open Multigraph in
theorem edges_eq_nil_eq {u w : V} (p : G.Walk u w) (h : p.edges = []) : u = w := by
  cases p with
  | nil => rfl
  | cons e h' p => simp [Walk.edges] at h

open Multigraph in
theorem eq_nil_of_edges {u : V} (p : G.Walk u u) (h : p.edges = []) : p = Walk.nil u := by
  cases p with
  | nil => rfl
  | cons e h' p => simp [Walk.edges] at h

open Multigraph in
/-- A prefix whose end vertex reappears in the rest has no edges. -/
theorem prefix_nil {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
    (hnd : (p.append q).support.Nodup) (hu : u ∈ q.support) : p.edges = [] := by
  cases p with
  | nil => rfl
  | cons e h p' =>
    exfalso
    simp only [Walk.append, Walk.support] at hnd
    rw [List.nodup_cons] at hnd
    exact hnd.1 (mem_append_right p' q hu)

open Multigraph in
/-- A suffix whose start reappears in the prefix has no edges. -/
theorem suffix_nil {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
    (hnd : (p.append q).support.Nodup) (hw : w ∈ p.support) : q.edges = [] := by
  induction p with
  | nil v' =>
    simp only [Walk.support, List.mem_singleton] at hw
    subst hw
    -- closed walk with nodup support
    cases q with
    | nil => rfl
    | cons e h q' =>
      exfalso
      simp only [Walk.append, Walk.support] at hnd
      rw [List.nodup_cons] at hnd
      exact hnd.1 (end_mem q')
  | cons e h p ih =>
    simp only [Walk.append, Walk.support] at hnd hw
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.1 hw with hw | hw
    · exfalso
      subst hw
      exact hnd.1 (mem_append_right p q (end_mem q))
    · exact ih q hnd.2 hw

open Multigraph in
theorem append_nil {u w : V} (p : G.Walk u w) : p.append (Walk.nil w) = p := by
  induction p with
  | nil _ => rfl
  | cons e h p ih => simp [Walk.append, ih]

open Multigraph in
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by
  induction p with
  | nil _ => simp [Walk.append, Walk.reverse, append_nil]
  | cons e h p ih =>
    simp only [Walk.append, Walk.reverse, ih, append_assoc]

open Multigraph in
theorem support_length {u w : V} (p : G.Walk u w) : p.support.length = p.edges.length + 1 := by
  induction p with
  | nil _ => simp [Walk.support, Walk.edges]
  | cons e h p ih => simp [Walk.support, Walk.edges, ih]

open Multigraph in
theorem support_head {u w : V} (p : G.Walk u w) : ∃ tl, p.support = u :: tl := by
  cases p <;> simp [Walk.support]

open Multigraph in
theorem getElem_split {a t b : V} (w₁ : G.Walk a t) (w₂ : G.Walk t b) :
    ∃ h : w₁.edges.length < (w₁.append w₂).support.length,
      (w₁.append w₂).support[w₁.edges.length] = t := by
  have hl : (w₁.append w₂).support.length = w₁.edges.length + w₂.edges.length + 1 := by
    rw [support_append, List.length_append, List.length_dropLast, support_length, support_length]
    omega
  refine ⟨by omega, ?_⟩
  obtain ⟨tl, htl⟩ := support_head w₂
  simp only [support_append]
  rw [List.getElem_append_right (by rw [List.length_dropLast, support_length]; omega)]
  simp [List.length_dropLast, support_length, htl]

open Multigraph in
/-- Two decompositions of a path at the same vertex have the same first part (as edge lists). -/
theorem uniq {a t b : V} (w₁ w₁' : G.Walk a t) (w₂ w₂' : G.Walk t b)
    (h : w₁.append w₂ = w₁'.append w₂') (hnd : (w₁.append w₂).support.Nodup) :
    w₁.edges = w₁'.edges := by
  obtain ⟨hb, hv⟩ := getElem_split w₁ w₂
  obtain ⟨hb', hv'⟩ := getElem_split w₁' w₂'
  have h1 : (w₁.append w₂).support = (w₁'.append w₂').support := by rw [h]
  have : w₁.edges.length = w₁'.edges.length := by
    have hb'' : w₁'.edges.length < (w₁.append w₂).support.length := by rw [h1]; exact hb'
    have := (hnd.getElem_inj_iff (hi := hb) (hj := hb'')).1 (by
      rw [hv]; simp only [h1]; exact hv'.symm)
    exact this
  have he : w₁.edges ++ w₂.edges = w₁'.edges ++ w₂'.edges := by
    rw [← edges_append, ← edges_append, h]
  exact (List.append_inj he this).1

open Multigraph in
/-- A path meeting `p` in a common subpath, starting at the start of `p`, is the initial piece of
`p` up to its end vertex. -/
theorem sp {a b t : V} (p : G.Walk a b) (hp : p.support.Nodup) (q : G.Walk a t)
    (hq : q.support.Nodup) (hm : p.MeetInSubpath q) (p1 : G.Walk a t) (p2 : G.Walk t b)
    (hpp : p = p1.append p2) : q.edges = p1.edges := by
  have hta : t ∈ p.support := by rw [hpp]; exact mem_append_right p1 p2 (start_mem p2)
  rcases hm with hd | ⟨x, y, r, hI, hrp, hrq⟩
  · exact absurd (start_mem q) (hd a (start_mem p))
  · have ha : a ∈ r.support := (hI.1 a).2 ⟨start_mem p, start_mem q⟩
    have ht : t ∈ r.support := (hI.1 t).2 ⟨hta, end_mem q⟩
    obtain ⟨p₁', p₂', hpe⟩ := hrp
    have e1 : p₁'.edges = [] :=
      prefix_nil p₁' (r.append p₂') (hpe ▸ hp) (mem_append_left r p₂' ha)
    have hax : a = x := edges_eq_nil_eq _ e1
    subst hax
    have p1eq : p₁' = Walk.nil a := eq_nil_of_edges p₁' e1
    have hp' : p = r.append p₂' := by rw [hpe, p1eq]; rfl
    rcases hrq with hrq | hrq
    · obtain ⟨q₁, q₂, hqe⟩ := hrq
      have e2 : q₁.edges = [] :=
        prefix_nil q₁ (r.append q₂) (hqe ▸ hq) (mem_append_left r q₂ ha)
      have hnd : ((q₁.append r).append q₂).support.Nodup := by
        rw [append_assoc, ← hqe]; exact hq
      have e3 : q₂.edges = [] :=
        suffix_nil (q₁.append r) q₂ hnd (mem_append_right q₁ r ht)
      have hyt : t = y := (edges_eq_nil_eq q₂ e3).symm
      subst hyt
      have hu : r.edges = p1.edges := by
        refine uniq r p1 p₂' p2 (by rw [← hp', hpp]) (by rw [← hp']; exact hp)
      rw [hqe, edges_append, edges_append, e2, e3, List.nil_append, List.append_nil]
      exact hu
    · obtain ⟨q₁, q₂, hqe⟩ := hrq
      have ha' : a ∈ r.reverse.support := by rw [support_reverse]; simpa using ha
      have ht' : t ∈ r.reverse.support := by rw [support_reverse]; simpa using ht
      have e2 : q₁.edges = [] :=
        prefix_nil q₁ (r.reverse.append q₂) (hqe ▸ hq) (mem_append_left r.reverse q₂ ha')
      have hnd : ((q₁.append r.reverse).append q₂).support.Nodup := by
        rw [append_assoc, ← hqe]; exact hq
      have e3 : q₂.edges = [] :=
        suffix_nil (q₁.append r.reverse) q₂ hnd (mem_append_right q₁ r.reverse ht')
      have hat : a = t := edges_eq_nil_eq q₂ e3
      subst hat
      have hq0 : q.edges = [] := by
        refine suffix_nil (Walk.nil a) q ?_ (by simp [Walk.support])
        simpa [Walk.append] using hq
      have hp0 : p1.edges = [] := by
        refine prefix_nil p1 p2 (hpp ▸ hp) (start_mem p2)
      rw [hq0, hp0]

open Classical in
/-- The number of ends at `t` of an unordered pair (a loop counts twice). -/
noncomputable def sdeg (t : V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun a b => (if a = t then 1 else 0) + (if b = t then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

open Classical in
theorem sdeg_mk (t a b : V) :
    sdeg t s(a, b) = (if a = t then 1 else 0) + (if b = t then 1 else 0) := rfl

open Multigraph Classical in
theorem inc_walk (t : V) {u w : V} (p : G.Walk u w) :
    (p.edges.map (fun e => sdeg t (G.ends e))).sum + (if u = t then 1 else 0) +
      (if w = t then 1 else 0) = 2 * p.support.count t := by
  induction p with
  | nil v => by_cases h : v = t <;> simp [Walk.edges, Walk.support, h]
  | cons e h p ih =>
    rename_i u' v' w'
    simp only [Walk.edges, Walk.support, List.map_cons, List.sum_cons, h, sdeg_mk,
      List.count_cons]
    by_cases h1 : u' = t <;> by_cases h2 : v' = t <;> by_cases h3 : w' = t <;>
      simp_all <;> omega

open Multigraph in
theorem exists_split {u w v : V} (p : G.Walk u w) (hv : v ∈ p.support) :
    ∃ (p1 : G.Walk u v) (p2 : G.Walk v w), p = p1.append p2 := by
  induction p with
  | nil x =>
    simp only [Walk.support, List.mem_singleton] at hv
    subst hv; exact ⟨Walk.nil _, Walk.nil _, rfl⟩
  | cons e h p ih =>
    rename_i u' v' w'
    simp only [Walk.support, List.mem_cons] at hv
    rcases hv with hv | hv
    · subst hv; exact ⟨Walk.nil _, Walk.cons e h p, rfl⟩
    · obtain ⟨p1, p2, hp⟩ := ih hv
      exact ⟨Walk.cons e h p1, p2, by rw [hp]; rfl⟩

end RepellingPairs.Dev.FlowNormWalk
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.FlowNormPath

open RepellingPairs RepellingPairs.Dev.FlowNormWalk


variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

theorem term_inj (G : OSInstance V E k) : Function.Injective G.term := by
  intro i j hij
  have h1 := G.pos_term i
  have h2 := G.pos_term j
  rw [hij] at h1
  have h3 : Complex.exp ((G.θ i : ℂ) * Complex.I) = Complex.exp ((G.θ j : ℂ) * Complex.I) := by
    rw [← h1, ← h2]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  have hn2 : G.θ i = G.θ j + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hpi := Real.pi_pos
  have a1 := G.θ_nonneg i
  have a2 := G.θ_nonneg j
  have b1 := G.θ_lt_two_pi i
  have b2 := G.θ_lt_two_pi j
  have hn3 : (n : ℝ) < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hn4 : (-1 : ℝ) < n := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hn5 : n = 0 := by
    have : n < 1 := by exact_mod_cast hn3
    have : -1 < n := by exact_mod_cast hn4
    omega
  subst hn5
  have : G.θ i = G.θ j := by simpa using hn2
  exact G.θ_strictMono.injective this

theorem closed_edges {x : V} (p : G.graph.Walk x x) (hp : p.support.Nodup) : p.edges = [] :=
  suffix_nil (Multigraph.Walk.nil x) p (by simpa [Multigraph.Walk.append] using hp)
    (by simp [Multigraph.Walk.support])

theorem path_ne_nil (P : PathStructure G) {i j : Fin k} (h : i ≠ j) :
    (P.path i j).1.edges ≠ [] := by
  intro he
  exact h (term_inj G (edges_eq_nil_eq _ he))

theorem path_self_support (P : PathStructure G) (i : Fin k) :
    (P.path i i).1.support = [G.term i] := by
  have h := closed_edges (P.path i i).1 (P.path i i).2
  rw [eq_nil_of_edges _ h]
  simp [Multigraph.Walk.support]

theorem path_self_edges (P : PathStructure G) (i : Fin k) : (P.path i i).1.edges = [] :=
  closed_edges (P.path i i).1 (P.path i i).2

theorem tpath_self_edges (q : TerminalPath G) (h : q.src = q.tgt) : q.path.1.edges = [] := by
  obtain ⟨s, t, p⟩ := q
  simp only at h
  subst h
  exact closed_edges p.1 p.2

/-- Splitting a designated path at an interior terminal splits its edges. -/
theorem split_edges (P : PathStructure G) (a b t : Fin k)
    (ht : G.term t ∈ (P.path a b).1.support) :
    (P.path a b).1.edges = (P.path a t).1.edges ++ (P.path t b).1.edges := by
  obtain ⟨p1, p2, hpp⟩ := exists_split (P.path a b).1 ht
  have e1 : (P.path a t).1.edges = p1.edges :=
    sp (P.path a b).1 (P.path a b).2 (P.path a t).1 (P.path a t).2 (P.meet a b a t) p1 p2 hpp
  have hrev : (P.path b a).1 = p2.reverse.append p1.reverse := by
    rw [P.path_symm a b, hpp, reverse_append]
  have e2 : (P.path b t).1.edges = p2.reverse.edges :=
    sp (P.path b a).1 (by rw [P.path_symm a b, support_reverse]; exact List.nodup_reverse.2 (P.path a b).2)
      (P.path b t).1 (P.path b t).2 (P.meet b a b t) p2.reverse p1.reverse hrev
  rw [P.path_symm t b, edges_reverse, edges_reverse] at e2
  have e3 : (P.path t b).1.edges = p2.edges := List.reverse_inj.1 e2
  rw [hpp, edges_append, e1, e3]

theorem tight (P : PathStructure G) {D : Fin k → Fin k → ℝ} (hD : IsMetric D)
    (hgood : P.IsGood D) (a b t : Fin k) (ht : G.term t ∈ (P.path a b).1.support) :
    D a b = D a t + D t b := by
  have hnr : ¬ Repel D a b t t := by
    intro hr
    have hd := hgood a b t t hr (G.term t) ht
    rw [path_self_support] at hd
    exact hd (by simp)
  unfold Repel at hnr
  rw [not_lt, max_le_iff] at hnr
  have h1 := hnr.1
  rw [hD.self, add_zero, hD.symm b t] at h1
  have h2 := hD.triangle a t b
  linarith

end RepellingPairs.Dev.FlowNormPath
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.FlowNormComb

open RepellingPairs RepellingPairs.Dev.FlowNormWalk RepellingPairs.Dev.FlowNormPath


section generic

theorem sum_count {E : Type*} [Fintype E] [DecidableEq E] (f : E → ℕ) (l : List E) :
    ∑ e, f e * l.count e = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons, ← ih]
    have : ∀ e, f e * (l.count e + if (a == e) = true then 1 else 0) =
        f e * l.count e + if a = e then f e else 0 := by
      intro e; by_cases h : a = e <;> simp [h] <;> ring
    simp_rw [this, Finset.sum_add_distrib]
    simp [add_comm]

theorem sum_multi {ι α M : Type*} [AddCommMonoid M] (s : Finset ι) (m : ι → ℕ) (a : ι → α)
    (g : α → M) :
    (((∑ x ∈ s, m x • ({a x} : Multiset α)).map g).sum) = ∑ x ∈ s, m x • g (a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.map_add, Multiset.sum_add, ih]
    rw [Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

theorem mem_sum_multi {ι α : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → α) (y : α)
    (hy : y ∈ ∑ x ∈ s, m x • ({a x} : Multiset α)) : ∃ x ∈ s, m x ≠ 0 ∧ y = a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hy
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Multiset.mem_add] at hy
    rcases hy with hy | hy
    · rcases Nat.eq_zero_or_pos (m i) with h | h
      · simp [h] at hy
      · simp [Multiset.mem_nsmul, h.ne'] at hy
        exact ⟨i, Finset.mem_insert_self _ _, h.ne', hy⟩
    · obtain ⟨x, h1, h2, h3⟩ := ih hy
      exact ⟨x, Finset.mem_insert_of_mem h1, h2, h3⟩

end generic

section flow

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

theorem load_cons [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (F : DesignatedFlow k)
    (e : E) : DesignatedFlow.load P (a ::ₘ F) e =
      (P.path a.1 a.2).1.edges.count e + DesignatedFlow.load P F e := by
  simp [DesignatedFlow.load]

theorem pload_cons [DecidableEq E] (q : TerminalPath G) (F : PathFlow G) (e : E) :
    PathFlow.load (q ::ₘ F) e = q.path.1.edges.count e + PathFlow.load F e := by
  simp [PathFlow.load]

theorem cost_cons {D : Fin k → Fin k → ℝ} (a : Fin k × Fin k) (F : DesignatedFlow k) :
    DesignatedFlow.cost D (a ::ₘ F) = D a.1 a.2 + DesignatedFlow.cost D F := by
  simp [DesignatedFlow.cost]

theorem deg_chords (F : DesignatedFlow k) (t : Fin k) :
    Config.deg (DesignatedFlow.chords F) t =
      (F.map fun p => (if p.1 = t then 1 else 0) + (if p.2 = t then 1 else 0)).sum := by
  simp [DesignatedFlow.chords, Config.deg, Multiset.map_map, Function.comp_def, Config.chordDeg]

theorem pdeg_chords (F : PathFlow G) (t : Fin k) :
    Config.deg (PathFlow.chords F) t =
      (F.map fun q => (if q.src = t then 1 else 0) + (if q.tgt = t then 1 else 0)).sum := by
  simp [PathFlow.chords, Config.deg, Multiset.map_map, Function.comp_def, Config.chordDeg]

theorem wload_D [Fintype E] [DecidableEq E] (P : PathStructure G) (f : E → ℕ) (F : DesignatedFlow k) :
    ∑ e, f e * DesignatedFlow.load P F e =
      (F.map fun u => (((P.path u.1 u.2).1.edges).map f).sum).sum := by
  induction F using Multiset.induction_on with
  | empty => simp [DesignatedFlow.load]
  | cons a F ih =>
    simp only [load_cons, mul_add, Finset.sum_add_distrib, ih, sum_count, Multiset.map_cons,
      Multiset.sum_cons]

theorem wload_P [Fintype E] [DecidableEq E] (f : E → ℕ) (F : PathFlow G) :
    ∑ e, f e * PathFlow.load F e = (F.map fun q => ((q.path.1.edges).map f).sum).sum := by
  induction F using Multiset.induction_on with
  | empty => simp [PathFlow.load]
  | cons a F ih =>
    simp only [pload_cons, mul_add, Finset.sum_add_distrib, ih, sum_count, Multiset.map_cons,
      Multiset.sum_cons]

section internal

variable [Fintype V] [Fintype E] [DecidableEq E] {P : PathStructure G}

open Classical in
theorem exists_internal (F : DesignatedFlow k) (F' : PathFlow G)
    (hn1 : NoTrivialPair F) (hn2 : ∀ q ∈ F', q.src ≠ q.tgt) (hp2 : Property2 P F F') (t : Fin k)
    (h : Config.deg (DesignatedFlow.chords F) t < Config.deg (PathFlow.chords F') t) :
    ∃ u ∈ F, G.term t ∈ (P.path u.1 u.2).1.support ∧ u.1 ≠ t ∧ u.2 ≠ t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨dg, hdg⟩ : ∃ dg : E → ℕ, ∀ e, dg e = sdeg (G.term t) (G.graph.ends e) :=
    ⟨fun e => sdeg (G.term t) (G.graph.ends e), fun _ => rfl⟩
  have hmap : ∀ l : List E, l.map (fun e => sdeg (G.term t) (G.graph.ends e)) = l.map dg :=
    fun l => List.map_congr_left fun e _ => (hdg e).symm
  have hle : ∑ e, dg e * PathFlow.load F' e ≤ ∑ e, dg e * DesignatedFlow.load P F e :=
    Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (hp2 e)
  rw [wload_D, wload_P] at hle
  have hF : (F.map fun u => (((P.path u.1 u.2).1.edges).map dg).sum) =
      F.map fun p => (if p.1 = t then 1 else 0) + (if p.2 = t then 1 else 0) := by
    refine Multiset.map_congr rfl fun u hu => ?_
    have h1 := inc_walk (G.term t) (P.path u.1 u.2).1
    have hnd : (P.path u.1 u.2).1.support.Nodup := (P.path u.1 u.2).2
    have hne := hn1 u hu
    have e1 : (if G.term u.1 = G.term t then 1 else 0) = (if u.1 = t then 1 else 0) := by
      simp [(term_inj G).eq_iff]
    have e2 : (if G.term u.2 = G.term t then 1 else 0) = (if u.2 = t then 1 else 0) := by
      simp [(term_inj G).eq_iff]
    rw [e1, e2, hmap] at h1
    by_cases hm : G.term t ∈ (P.path u.1 u.2).1.support
    · have hc : (P.path u.1 u.2).1.support.count (G.term t) = 1 :=
        List.count_eq_one_of_mem hnd hm
      rw [hc] at h1
      have hh := hcon u hu hm
      by_cases a1 : u.1 = t <;> by_cases a2 : u.2 = t <;> simp_all <;> omega
    · have hc : (P.path u.1 u.2).1.support.count (G.term t) = 0 := List.count_eq_zero.2 hm
      rw [hc] at h1
      have a1 : u.1 ≠ t := fun h => hm (h ▸ start_mem _)
      have a2 : u.2 ≠ t := fun h => hm (h ▸ end_mem _)
      rw [if_neg a1, if_neg a2] at h1 ⊢; omega
  have hF' : ∀ q ∈ F', (if q.src = t then 1 else 0) + (if q.tgt = t then 1 else 0) ≤
      ((q.path.1.edges).map dg).sum := by
    intro q hq
    have h1 := inc_walk (G.term t) q.path.1
    have hnd : q.path.1.support.Nodup := q.path.2
    have hne := hn2 q hq
    have e1 : (if G.term q.src = G.term t then 1 else 0) = (if q.src = t then 1 else 0) := by
      simp [(term_inj G).eq_iff]
    have e2 : (if G.term q.tgt = G.term t then 1 else 0) = (if q.tgt = t then 1 else 0) := by
      simp [(term_inj G).eq_iff]
    rw [e1, e2, hmap] at h1
    by_cases hm : G.term t ∈ q.path.1.support
    · have hc : q.path.1.support.count (G.term t) = 1 := List.count_eq_one_of_mem hnd hm
      rw [hc] at h1
      by_cases a1 : q.src = t
      · by_cases a2 : q.tgt = t
        · exact absurd (a1.trans a2.symm) hne
        · rw [if_pos a1, if_neg a2] at h1 ⊢; omega
      · by_cases a2 : q.tgt = t
        · rw [if_neg a1, if_pos a2] at h1 ⊢; omega
        · rw [if_neg a1, if_neg a2]; omega
    · have hc : q.path.1.support.count (G.term t) = 0 := List.count_eq_zero.2 hm
      rw [hc] at h1
      have a1 : q.src ≠ t := fun h => hm (h ▸ start_mem _)
      have a2 : q.tgt ≠ t := fun h => hm (h ▸ end_mem _)
      simp [a1, a2]
  have key : Config.deg (PathFlow.chords F') t ≤ Config.deg (DesignatedFlow.chords F) t := by
    rw [pdeg_chords, deg_chords, ← hF]
    exact (Multiset.sum_map_le_sum_map _ _ hF').trans hle
  omega

end internal

section step

variable {P : PathStructure G}

/-- The invariant of the normalization process. -/
def Sol [DecidableEq E] (P : PathStructure G) (D : Fin k → Fin k → ℝ) (F : DesignatedFlow k) (F' : PathFlow G) :
    Prop :=
  NoTrivialPair F ∧ (∀ q ∈ F', q.src ≠ q.tgt) ∧ (∀ e, F'.load e ≤ F.load P e) ∧
    Property3 D F F' ∧ (∀ t, Even (Config.deg (DesignatedFlow.chords F) t)) ∧
    (∀ t, Even (Config.deg (PathFlow.chords F') t))

/-- The measure: total number of edges beyond one per unit. -/
def Nm (P : PathStructure G) (F : DesignatedFlow k) : ℕ :=
  (F.map fun u => (P.path u.1 u.2).1.edges.length - 1).sum

theorem split_step [DecidableEq E] {D : Fin k → Fin k → ℝ} (hD : IsMetric D)
    (hgood : P.IsGood D) (F : DesignatedFlow k) (F' : PathFlow G) (hS : Sol P D F F')
    (a b t : Fin k) (hu : (a, b) ∈ F) (hm : G.term t ∈ (P.path a b).1.support)
    (h1 : a ≠ t) (h2 : b ≠ t) :
    ∃ F2, Sol P D F2 F' ∧ Nm P F2 < Nm P F := by
  obtain ⟨R, hR⟩ : ∃ R, F = (a, b) ::ₘ R := ⟨F.erase (a, b), (Multiset.cons_erase hu).symm⟩
  subst hR
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hS
  have hsplit := split_edges P a b t hm
  have hT := tight P hD hgood a b t hm
  have hl1 : 0 < (P.path a t).1.edges.length := List.length_pos_iff.2 (path_ne_nil P h1)
  have hl2 : 0 < (P.path t b).1.edges.length := List.length_pos_iff.2 (path_ne_nil P (Ne.symm h2))
  have hlen : (P.path a b).1.edges.length =
      (P.path a t).1.edges.length + (P.path t b).1.edges.length := by
    rw [hsplit, List.length_append]
  refine ⟨(a, t) ::ₘ (t, b) ::ₘ R, ⟨?_, n2, ?_, ?_, ?_, n6⟩, ?_⟩
  · intro p hp
    simp only [Multiset.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact h1
    · exact Ne.symm h2
    · exact n1 p (Multiset.mem_cons_of_mem hp)
  · intro e
    have := n3 e
    simp only [load_cons] at this ⊢
    rw [hsplit, List.count_append] at this
    omega
  · unfold Property3 at n4 ⊢
    simp only [cost_cons] at n4 ⊢
    linarith
  · intro t'
    have := n5 t'
    rw [deg_chords] at this ⊢
    simp only [Multiset.map_cons, Multiset.sum_cons] at this ⊢
    obtain ⟨r, hr⟩ := this
    refine ⟨r + (if t = t' then 1 else 0), ?_⟩
    omega
  · unfold Nm
    simp only [Multiset.map_cons, Multiset.sum_cons]
    omega

end step

section final

variable {P : PathStructure G}

/-- The trivial path at a terminal. -/
def triv (G : OSInstance V E k) (t : Fin k) : TerminalPath G :=
  ⟨t, t, ⟨Multigraph.Walk.nil (G.term t), by simp [Multigraph.Walk.IsPath, Multigraph.Walk.support]⟩⟩

theorem finish [DecidableEq E] {D : Fin k → Fin k → ℝ} (hD : IsMetric D)
    (F : DesignatedFlow k) (F' : PathFlow G) (hS : Sol P D F F')
    (hall : ∀ t, Config.deg (PathFlow.chords F') t ≤ Config.deg (DesignatedFlow.chords F) t) :
    ∃ (F₁ : DesignatedFlow k) (F₁' : PathFlow G),
      Property2 P F₁ F₁' ∧ Property3 D F₁ F₁' ∧ Property4 F₁ F₁' ∧ NoTrivialPair F₁ := by
  classical
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hS
  let m : Fin k → ℕ := fun t =>
    (Config.deg (DesignatedFlow.chords F) t - Config.deg (PathFlow.chords F') t) / 2
  let T : PathFlow G := ∑ t : Fin k, m t • ({triv G t} : Multiset (TerminalPath G))
  refine ⟨F, F' + T, ?_, ?_, ?_, n1⟩
  · intro e
    have : PathFlow.load T e = 0 := by
      unfold PathFlow.load
      rw [sum_multi (Finset.univ) m (triv G) (fun q => q.path.1.edges.count e)]
      simp [triv, Multigraph.Walk.edges]
    have h2 : PathFlow.load (F' + T) e = PathFlow.load F' e + PathFlow.load T e := by
      simp [PathFlow.load, Multiset.map_add]
    rw [h2, this]; simpa using n3 e
  · unfold Property3 at n4 ⊢
    have : PathFlow.cost D T = 0 := by
      unfold PathFlow.cost
      rw [sum_multi (Finset.univ) m (triv G) (fun q => D q.src q.tgt)]
      simp [triv, hD.self]
    have h2 : PathFlow.cost D (F' + T) = PathFlow.cost D F' + PathFlow.cost D T := by
      simp [PathFlow.cost, Multiset.map_add]
    rw [h2, this]; linarith
  · intro t'
    rw [pdeg_chords, deg_chords]
    have h2 : ((F' + T).map fun q => (if q.src = t' then 1 else 0) + (if q.tgt = t' then 1 else 0)).sum =
        (F'.map fun q => (if q.src = t' then 1 else 0) + (if q.tgt = t' then 1 else 0)).sum +
        (T.map fun q => (if q.src = t' then 1 else 0) + (if q.tgt = t' then 1 else 0)).sum := by
      rw [Multiset.map_add, Multiset.sum_add]
    have h3 : (T.map fun q => (if q.src = t' then 1 else 0) + (if q.tgt = t' then 1 else 0)).sum =
        2 * m t' := by
      rw [sum_multi (Finset.univ) m (triv G) (fun q => (if q.src = t' then 1 else 0) + (if q.tgt = t' then 1 else 0))]
      rw [Finset.sum_eq_single t']
      · simp [triv]; ring
      · intro b _ hb; simp [triv, hb]
      · simp
    rw [h2, h3]
    have a1 := hall t'
    have a2 := n5 t'
    have a3 := n6 t'
    rw [pdeg_chords] at a1 a3
    rw [deg_chords] at a1 a2
    obtain ⟨r1, hr1⟩ := a2
    obtain ⟨r2, hr2⟩ := a3
    show _ = _
    simp only [m]
    rw [pdeg_chords, deg_chords]
    omega

end final

section induct

variable {P : PathStructure G}

theorem normalize [Fintype V] [Fintype E] [DecidableEq E] {D : Fin k → Fin k → ℝ} (hD : IsMetric D)
    (hgood : P.IsGood D) :
    ∀ (n : ℕ) (F : DesignatedFlow k) (F' : PathFlow G), Nm P F = n → Sol P D F F' →
    ∃ (F₁ : DesignatedFlow k) (F₁' : PathFlow G),
      Property2 P F₁ F₁' ∧ Property3 D F₁ F₁' ∧ Property4 F₁ F₁' ∧ NoTrivialPair F₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F F' hn hS
    by_cases hall : ∀ t, Config.deg (PathFlow.chords F') t ≤ Config.deg (DesignatedFlow.chords F) t
    · exact finish hD F F' hS hall
    · push Not at hall
      obtain ⟨t, ht⟩ := hall
      obtain ⟨u, hu, hm, h1, h2⟩ :=
        exists_internal F F' hS.1 hS.2.1 hS.2.2.1 t ht
      obtain ⟨F2, hS2, hlt⟩ := split_step hD hgood F F' hS u.1 u.2 t hu hm h1 h2
      exact ih (Nm P F2) (hn ▸ hlt) F2 F' rfl hS2

end induct

end flow

end RepellingPairs.Dev.FlowNormComb
end

section
set_option autoImplicit false

namespace RepellingPairs.Dev.FlowNorm

open RepellingPairs RepellingPairs.Dev.FlowNormWalk RepellingPairs.Dev.FlowNormPath
  RepellingPairs.Dev.FlowNormComb RepellingPairs.Dev.FlowNormRat


theorem sum_offdiag {k : ℕ} (f : Fin k × Fin k → ℝ) (hf : ∀ x : Fin k × Fin k, x.1 = x.2 → f x = 0) :
    ∑ i, ∑ j, f (i, j) = ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, f p.1 := by
  classical
  have h0 : ∑ i, ∑ j, f (i, j) = ∑ x : Fin k × Fin k, f x := (Fintype.sum_prod_type f).symm
  have h1 : ∑ x : Fin k × Fin k, f x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin k × Fin k => x.1 ≠ x.2), f x :=
    (Finset.sum_filter_of_ne (fun x _ hx => by
      by_contra h; exact hx (hf x (by simpa using h)))).symm
  have h2 : ∑ x ∈ Finset.univ.filter (fun x : Fin k × Fin k => x.1 ≠ x.2), f x =
      ∑ x : {x : Fin k × Fin k // x.1 ≠ x.2}, f x.1 :=
    Finset.sum_subtype _ (by simp) f
  rw [h0, h1, h2]

theorem sum_support_filter {α : Type*} [DecidableEq α] (F' : α →₀ ℝ) (pr : α → Prop) [DecidablePred pr]
    (g : α → ℝ) (hg : ∀ q, ¬ pr q → g q = 0) :
    F'.sum (fun q w => w * g q) = ∑ q : ↥(F'.support.filter pr), F' q.1 * g q.1 := by
  rw [Finsupp.sum, Finset.sum_coe_sort (F'.support.filter pr) (fun q => F' q * g q)]
  symm
  exact Finset.sum_filter_of_ne (fun x _ hx => by
    by_contra h; exact hx (by rw [hg x h, mul_zero]))

theorem even_sum_smul {ι : Type*} (s : Finset ι) (n : ι → ℕ) (x : ι → ℕ) :
    Even (∑ i ∈ s, (2 * n i) • x i) := by
  refine ⟨∑ i ∈ s, n i * x i, ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; ring

section main

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

open Classical in
theorem integral_exists [Fintype E] [DecidableEq E] (P : PathStructure G) {D : Fin k → Fin k → ℝ}
    (hD : IsMetric D) (F : Fin k → Fin k → ℝ) (F' : TerminalPath G →₀ ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hF' : ∀ q, 0 ≤ F' q)
    (hload : ∀ e, realPathLoad F' e ≤ realLoad P F e)
    (hcost : realCost D F < realPathCost D F') :
    ∃ (F₀ : DesignatedFlow k) (F₀' : PathFlow G), Sol P D F₀ F₀' := by
  let S : Finset (TerminalPath G) := F'.support.filter (fun q => q.src ≠ q.tgt)
  let cnt : (Fin k × Fin k) → E → ℕ := fun p e => (P.path p.1 p.2).1.edges.count e
  let cntq : TerminalPath G → E → ℕ := fun q e => q.path.1.edges.count e
  let ν := {p : Fin k × Fin k // p.1 ≠ p.2} ⊕ ↥S
  let z : ν → ℝ := Sum.elim (fun p => F p.1.1 p.1.2) (fun q => F' q.1)
  let c : ν → ℝ := Sum.elim (fun p => - D p.1.1 p.1.2) (fun q => D q.1.src q.1.tgt)
  let A : E → ν → ℤ := fun e => Sum.elim (fun p => -(cnt p.1 e : ℤ)) (fun q => (cntq q.1 e : ℤ))
  have hL : ∀ e, realLoad P F e = ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, F p.1.1 p.1.2 * (cnt p.1 e : ℝ) := by
    intro e
    have := sum_offdiag (fun x : Fin k × Fin k => F x.1 x.2 * (cnt x e : ℝ)) (by
      intro x hx
      have : cnt x e = 0 := by
        simp only [cnt]; rw [show x = (x.1, x.1) from Prod.ext rfl hx.symm]
        simp [path_self_edges]
      simp [this])
    exact this
  have hPL : ∀ e, realPathLoad F' e = ∑ q : ↥S, F' q.1 * (cntq q.1 e : ℝ) := by
    intro e
    exact sum_support_filter F' (fun q => q.src ≠ q.tgt) (fun q => (cntq q e : ℝ)) (by
      intro q hq
      have : cntq q e = 0 := by
        simp only [cntq]; rw [tpath_self_edges q (not_not.1 hq)]; simp
      simp [this])
  have hC : realCost D F = ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, F p.1.1 p.1.2 * D p.1.1 p.1.2 := by
    have := sum_offdiag (fun x : Fin k × Fin k => F x.1 x.2 * D x.1 x.2) (by
      intro x hx; simp [hx, hD.self])
    exact this
  have hPC : realPathCost D F' = ∑ q : ↥S, F' q.1 * D q.1.src q.1.tgt := by
    exact sum_support_filter F' (fun q => q.src ≠ q.tgt) (fun q => D q.src q.tgt) (by
      intro q hq
      rw [not_not.1 hq, hD.self])
  have hz : ∀ v, 0 ≤ z v := by
    rintro (p | q)
    · exact hF _ _
    · exact hF' _
  have hA : ∀ e, ∑ v, (A e v : ℝ) * z v ≤ 0 := by
    intro e
    rw [Fintype.sum_sum_type]
    simp only [A, z, Sum.elim_inl, Sum.elim_inr]
    have := hload e
    rw [hL, hPL] at this
    push_cast
    have e1 : ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, -(cnt p.1 e : ℝ) * F p.1.1 p.1.2 =
        -∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, F p.1.1 p.1.2 * (cnt p.1 e : ℝ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ q : ↥S, (cntq q.1 e : ℝ) * F' q.1 = ∑ q : ↥S, F' q.1 * (cntq q.1 e : ℝ) :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [e1, e2]; linarith
  have hc : 0 < ∑ v, c v * z v := by
    rw [Fintype.sum_sum_type]
    simp only [c, z, Sum.elim_inl, Sum.elim_inr]
    rw [hC, hPC] at hcost
    have e1 : ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, -D p.1.1 p.1.2 * F p.1.1 p.1.2 =
        -∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, F p.1.1 p.1.2 * D p.1.1 p.1.2 := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ q : ↥S, D q.1.src q.1.tgt * F' q.1 = ∑ q : ↥S, F' q.1 * D q.1.src q.1.tgt :=
      Finset.sum_congr rfl fun q _ => by ring
    rw [e1, e2]; linarith
  obtain ⟨n, hnA, hnc⟩ := exists_nat_solution A c z hz hA hc
  let F₀ : DesignatedFlow k :=
    ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, (2 * n (Sum.inl p)) • ({p.1} : Multiset (Fin k × Fin k))
  let F₀' : PathFlow G :=
    ∑ q : ↥S, (2 * n (Sum.inr q)) • ({q.1} : Multiset (TerminalPath G))
  refine ⟨F₀, F₀', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, _, _, hx⟩ := mem_sum_multi _ _ _ p hp
    rw [hx]; exact x.2
  · intro q hq
    obtain ⟨x, _, _, hx⟩ := mem_sum_multi _ _ _ q hq
    rw [hx]; exact (Finset.mem_filter.1 x.2).2
  · intro e
    have h1 : PathFlow.load F₀' e = ∑ q : ↥S, (2 * n (Sum.inr q)) • cntq q.1 e := by
      unfold PathFlow.load
      exact sum_multi (Finset.univ) (fun q => 2 * n (Sum.inr q)) (fun q : ↥S => q.1)
        (fun q => q.path.1.edges.count e)
    have h2 : DesignatedFlow.load P F₀ e =
        ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, (2 * n (Sum.inl p)) • cnt p.1 e := by
      unfold DesignatedFlow.load
      exact sum_multi (Finset.univ) (fun p => 2 * n (Sum.inl p))
        (fun p : {p : Fin k × Fin k // p.1 ≠ p.2} => p.1) (fun p => (P.path p.1 p.2).1.edges.count e)
    have := hnA e
    rw [Fintype.sum_sum_type] at this
    simp only [A, Sum.elim_inl, Sum.elim_inr] at this
    rw [h1, h2]
    have h3 : ∑ q : ↥S, (cntq q.1 e : ℝ) * (n (Sum.inr q) : ℝ) ≤
        ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, (cnt p.1 e : ℝ) * (n (Sum.inl p) : ℝ) := by
      push_cast at this
      have e1 : ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, -(cnt p.1 e : ℝ) * (n (Sum.inl p) : ℝ) =
          -∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, (cnt p.1 e : ℝ) * (n (Sum.inl p) : ℝ) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
      rw [e1] at this; linarith
    have h4 : ∑ q : ↥S, cntq q.1 e * n (Sum.inr q) ≤
        ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, cnt p.1 e * n (Sum.inl p) := by
      exact_mod_cast h3
    have h5 : ∀ (x y : ℕ), (2 * y) • x = 2 * (x * y) := fun x y => by rw [smul_eq_mul]; ring
    simp only [h5, ← Finset.mul_sum]
    omega
  · unfold Property3
    have h1 : PathFlow.cost D F₀' = ∑ q : ↥S, (2 * n (Sum.inr q)) • D q.1.src q.1.tgt := by
      unfold PathFlow.cost
      exact sum_multi (Finset.univ) (fun q => 2 * n (Sum.inr q)) (fun q : ↥S => q.1)
        (fun q => D q.src q.tgt)
    have h2 : DesignatedFlow.cost D F₀ =
        ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, (2 * n (Sum.inl p)) • D p.1.1 p.1.2 := by
      unfold DesignatedFlow.cost
      exact sum_multi (Finset.univ) (fun p => 2 * n (Sum.inl p))
        (fun p : {p : Fin k × Fin k // p.1 ≠ p.2} => p.1) (fun p => D p.1 p.2)
    rw [h1, h2]
    rw [Fintype.sum_sum_type] at hnc
    simp only [c, Sum.elim_inl, Sum.elim_inr] at hnc
    simp only [nsmul_eq_mul]
    push_cast
    have e1 : ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, -D p.1.1 p.1.2 * (n (Sum.inl p) : ℝ) =
        -∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, D p.1.1 p.1.2 * (n (Sum.inl p) : ℝ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
    rw [e1] at hnc
    have e2 : ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, 2 * (n (Sum.inl p) : ℝ) * D p.1.1 p.1.2 =
        2 * ∑ p : {p : Fin k × Fin k // p.1 ≠ p.2}, D p.1.1 p.1.2 * (n (Sum.inl p) : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have e3 : ∑ q : ↥S, 2 * (n (Sum.inr q) : ℝ) * D q.1.src q.1.tgt =
        2 * ∑ q : ↥S, D q.1.src q.1.tgt * (n (Sum.inr q) : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    rw [e2, e3]; linarith
  · intro t
    rw [deg_chords]
    unfold F₀
    rw [sum_multi (Finset.univ) (fun p => 2 * n (Sum.inl p))
      (fun p : {p : Fin k × Fin k // p.1 ≠ p.2} => p.1)
      (fun p => (if p.1 = t then 1 else 0) + (if p.2 = t then 1 else 0))]
    exact even_sum_smul _ _ _
  · intro t
    rw [pdeg_chords]
    unfold F₀'
    rw [sum_multi (Finset.univ) (fun q => 2 * n (Sum.inr q)) (fun q : ↥S => q.1)
      (fun q => (if q.src = t then 1 else 0) + (if q.tgt = t then 1 else 0))]
    exact even_sum_smul _ _ _

end main

end RepellingPairs.Dev.FlowNorm

namespace RepellingPairs


theorem chk_flow_normalization {V : Type u} {E : Type v} {k : ℕ} [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D)
    (F : Fin k → Fin k → ℝ) (F' : TerminalPath G →₀ ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hF' : ∀ q, 0 ≤ F' q)
    (hload : ∀ e, realPathLoad F' e ≤ realLoad P F e)
    (hcost : realCost D F < realPathCost D F') :
    ∃ (F₁ : DesignatedFlow k) (F₁' : PathFlow G),
      Property2 P F₁ F₁' ∧ Property3 D F₁ F₁' ∧ Property4 F₁ F₁' ∧ NoTrivialPair F₁ := by
  obtain ⟨F₀, F₀', hS⟩ := Dev.FlowNorm.integral_exists P hD F F' hF hF' hload hcost
  exact Dev.FlowNormComb.normalize hD hgood _ F₀ F₀' rfl hS

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_flow_normalization := @RepellingPairs.chk_flow_normalization
