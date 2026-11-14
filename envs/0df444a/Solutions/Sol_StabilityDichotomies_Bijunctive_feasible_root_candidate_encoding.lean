-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.feasible_root_candidate_encoding
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:24.178447+00:00
-- url     : https://prove2.me/submissions/82ded55d-4c4f-4a87-b4d3-74a81f5bf59e

import Theorems.Thm_StabilityDichotomies_Bijunctive_positive_winning_root_dominates_both_literals
import Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_opposites
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem distance_walk {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (a b : Literal V) (n : ℕ)
    (hd : implicationDistance rep G a b = some n) : WalkLength (implicationArc rep G) n a b := by
  unfold implicationDistance at hd
  split at hd
  next h =>
    have hn : Nat.find h = n := Option.some.inj hd
    simpa [← hn] using Nat.find_spec h
  next h => simp at hd

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F₀ : Instance Γ V) (v : V)
    (hG : ∀ c ∈ G.constraints, c ∈ F₀.constraints) :
    ∃ (C : Finset (Literal V)) (label : Literal V → Bool) (d : Literal V → ℝ),
      (∀ r ∈ C, 0 ≤ d r) ∧
      ∀ (F : Instance Γ V), (∀ c ∈ F₀.constraints, c ∈ F.constraints) → Satisfiable F →
      ∀ δ : Literal V → ℝ, (∀ r, 0 < δ r) →
        ∃ r ∈ C, feasibleLiteral F r ∧
          label r = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)) ∧
          0 < δ r - d r ∧
          ∀ q ∈ C, feasibleLiteral F q → δ q - d q ≤ δ r - d r := by
  classical
  let C : Finset (Literal V) := Finset.univ.filter (fun r => feasibleLiteral F₀ r ∧
    ∃ b n, implicationDistance rep G r (v,b) = some n)
  let label : Literal V → Bool := fun r => if ∃ n, implicationDistance rep G r (v,true) = some n then true else false
  let d : Literal V → ℝ := fun r => (implicationDistance rep G r (v,label r)).getD 0
  have hC (r : Literal V) : r ∈ C ↔ feasibleLiteral F₀ r ∧
      ∃ b n, implicationDistance rep G r (v,b) = some n := by simp [C]
  have hinfo (r : Literal V) (hr : r ∈ C) :
      ∃ n, implicationDistance rep G r (v,label r) = some n ∧ d r = n ∧
        ∀ z m, implicationDistance rep G r (v,z) = some m → z = label r ∧ m = n := by
    obtain ⟨hfeas,hreach⟩ := (hC r).mp hr
    by_cases ht : ∃ n, implicationDistance rep G r (v,true) = some n
    · obtain ⟨n,hn⟩ := ht
      have hl : label r = true := by simp [label,show ∃ n, implicationDistance rep G r (v,true) = some n from ⟨n,hn⟩]
      refine ⟨n,by simpa [hl] using hn,?_,?_⟩
      · simp [d,hl,hn]
      · intro z m hm
        cases z with
        | true => exact ⟨hl.symm,Option.some.inj (hm.symm.trans hn)⟩
        | false =>
          have hbad := feasible_root_cannot_reach_opposites rep G F₀ hG r (v,true) hfeas
          have hneg : literalNeg (v,true) = (v,false) := rfl
          exact False.elim (hbad ⟨n,m,distance_walk rep G r (v,true) n hn,
            by simpa [hneg] using distance_walk rep G r (v,false) m hm⟩)
    · obtain ⟨z,n,hn⟩ := hreach
      have hz : z = false := by
        cases z with
        | false => rfl
        | true => exact False.elim (ht ⟨n,hn⟩)
      subst z
      have hl : label r = false := by simp [label,ht]
      refine ⟨n,by simpa [hl] using hn,?_,?_⟩
      · simp [d,hl,hn]
      · intro z m hm
        cases z with
        | true => exact False.elim (ht ⟨m,hm⟩)
        | false => exact ⟨hl.symm,Option.some.inj (hm.symm.trans hn)⟩
  refine ⟨C,label,d,?_,?_⟩
  · intro r hr
    obtain ⟨n,_,hn,_⟩ := hinfo r hr
    rw [hn]
    positivity
  · intro F hFsub hFsat δ hδ
    have hGF : ∀ c ∈ G.constraints, c ∈ F.constraints := fun c hc => hFsub c (hG c hc)
    obtain ⟨r,n,w,hw,hfeas,hd,hpos,hval,hmax,_⟩ :=
      positive_winning_root_dominates_both_literals rep G F hFsat hGF δ hδ v
    have hr0 : feasibleLiteral F₀ r := by
      obtain ⟨x,hx,hxr⟩ := hfeas
      exact ⟨x,fun c hc => hx c (hFsub c hc),hxr⟩
    have hrC : r ∈ C := (hC r).mpr ⟨hr0,w,n,hd⟩
    obtain ⟨nr,_,hdr,huniq⟩ := hinfo r hrC
    obtain ⟨hlabel,hnr⟩ := huniq w n hd
    have hrD : d r = n := by rw [hdr,← hnr]
    refine ⟨r,hrC,hfeas,?_,?_,?_⟩
    · exact hlabel.symm.trans hw
    · simpa [hrD] using hval
    · intro q hq hqF
      obtain ⟨m,hm,hqd,_⟩ := hinfo q hq
      have hh := hmax q m (label q) hqF hm
      simpa [hqd,hrD] using hh
