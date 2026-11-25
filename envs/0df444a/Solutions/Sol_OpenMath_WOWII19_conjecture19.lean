-- Prove2me | solution 1 for OpenMath.WOWII19.conjecture19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:21.604868+00:00
-- url     : https://prove2.me/submissions/1c5357f0-4880-4d3f-87e4-8dea44b0ff1b

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
public import Theorems.Thm_OpenMath_WOWII19_bound_one
public import Theorems.Thm_OpenMath_WOWII19_bound_two
public import Theorems.Thm_OpenMath_dist_le_ecc
public import Theorems.Thm_OpenMath_exists_dist_eq_ecc


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}
namespace OpenMath.WOWII19
theorem _root_.solution (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  -- the vertex maximising local independence
  obtain ⟨vs, -, hvs⟩ := exists_max_image univ (indepNeighborsCard G) univ_nonempty
  set L := indepNeighborsCard G vs with hL
  have hsup : sSup (Set.range (indepNeighbors G)) = (L : ℝ) := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨vs, rfl⟩, ?_⟩
    rintro _ ⟨u, rfl⟩
    unfold indepNeighbors
    exact_mod_cast hvs u (mem_univ u)
  -- diameter
  obtain ⟨xd, -, hxd⟩ := exists_max_image univ (ecc G) univ_nonempty
  set D := ecc G xd with hD
  obtain ⟨yd, hyd⟩ := exists_dist_eq_ecc h_conn xd
  -- eccentricity of `vs`
  set e := ecc G vs with he
  have he1 : 1 ≤ e := by
    obtain ⟨a, b', hab⟩ := exists_pair_ne α
    by_contra hcon
    have h1 := dist_le_ecc h_conn vs a
    have h2 := dist_le_ecc h_conn vs b'
    have ha : a = vs := by
      by_contra hne
      have := h_conn.pos_dist_of_ne (Ne.symm hne)
      omega
    have hb : b' = vs := by
      by_contra hne
      have := h_conn.pos_dist_of_ne (Ne.symm hne)
      omega
    exact hab (ha.trans hb.symm)
  set avg := (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) with havg
  have hsum_le : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) ≤ Fintype.card α * (D : ℝ) := by
    have : ∀ v ∈ (univ : Finset α), ((G.eccent v).toNat : ℝ) ≤ D := fun v _ => by
      exact_mod_cast hxd v (mem_univ v)
    calc ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) ≤ ∑ v ∈ (univ : Finset α), (D : ℝ) :=
          sum_le_sum this
      _ = Fintype.card α * (D : ℝ) := by simp
  -- reduce to `avg + L < b + 1`
  rw [hsup]
  unfold b
  have key : avg + L < (largestInducedBipartiteSubgraphSize G : ℝ) + 1 := by
    by_cases hcase : avg ≤ e
    · have := bound_one h_conn vs he1
      have : (L : ℝ) + e ≤ largestInducedBipartiteSubgraphSize G := by exact_mod_cast this
      linarith
    · push_neg at hcase
      -- the average eccentricity is strictly below the diameter
      have hlt : avg < D := by
        have heD : (e : ℝ) < D := by
          have : avg ≤ D := by
            rw [havg, div_le_iff₀ hn]
            linarith
          linarith
        have hsum_lt : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) < Fintype.card α * (D : ℝ) := by
          have hsplit := Finset.add_sum_erase (univ : Finset α)
            (fun v => ((G.eccent v).toNat : ℝ)) (mem_univ vs)
          have hrest : ∑ v ∈ (univ : Finset α).erase vs, ((G.eccent v).toNat : ℝ)
              ≤ ((univ : Finset α).erase vs).card * (D : ℝ) := by
            calc ∑ v ∈ (univ : Finset α).erase vs, ((G.eccent v).toNat : ℝ)
                ≤ ∑ v ∈ (univ : Finset α).erase vs, (D : ℝ) :=
                  sum_le_sum fun v _ => by exact_mod_cast hxd v (mem_univ v)
              _ = ((univ : Finset α).erase vs).card * (D : ℝ) := by simp
          have hcard : (((univ : Finset α).erase vs).card : ℝ) + 1 = Fintype.card α := by
            rw [card_erase_of_mem (mem_univ vs), card_univ]
            have : 1 ≤ Fintype.card α := Fintype.card_pos
            push_cast [Nat.cast_sub this]
            ring
          have hev : ((G.eccent vs).toNat : ℝ) = e := rfl
          rw [← hsplit, hev]
          nlinarith
        rw [havg, div_lt_iff₀ hn]
        linarith
      -- choose the diametral pair so that `x` is the closer end
      have hb2 : L + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by
        rcases le_total (G.dist vs xd) (G.dist vs yd) with hxy | hxy
        · exact bound_two h_conn vs xd yd D hyd hxy he1
        · have hyx : G.dist yd xd = D := by rw [dist_comm]; exact hyd
          exact bound_two h_conn vs yd xd D hyx hxy he1
      have : (L : ℝ) + D ≤ largestInducedBipartiteSubgraphSize G + 1 := by exact_mod_cast hb2
      linarith
  have hfl : ⌊avg + (L : ℝ)⌋ ≤ (largestInducedBipartiteSubgraphSize G : ℤ) := by
    rw [Int.floor_le_iff]
    push_cast
    linarith
  exact_mod_cast hfl
end OpenMath.WOWII19
