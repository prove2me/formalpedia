-- Prove2me | solution 1 for RGMISFast.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T01:08:40.229868+00:00
-- url     : https://prove2.me/submissions/72f1976c-6db3-4ba2-b8e0-ff5882b6d240

import Theorems.Thm_RGMISFast_Ncount_measurable
import Theorems.Thm_RGMISFast_dsSum_measurable
import Theorems.Thm_RGMISFast_root_count_arrival_expansion
open MeasureTheory ProbabilityTheory RGMISFast
set_option autoImplicit false

open RGMISFast
set_option autoImplicit false

lemma singleton_attached_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (W : Finset V) :
    IsAttached G {u} W ↔ u ∉ W ∧ IsRootConnected G u (insert u W) := by
  classical
  constructor
  · rintro ⟨hd,hr⟩
    have hu : u ∉ W := by simpa using hd
    refine ⟨hu,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact .refl _
    · obtain ⟨y,hy,hyx⟩ := hr x hx
      have he : y = u := Finset.mem_singleton.mp hy
      subst y
      simpa using hyx
  · rintro ⟨hu,hroot⟩
    refine ⟨by simpa using hu,?_⟩
    intro w hw
    exact ⟨u,Finset.mem_singleton_self _,by simpa using hroot.2 w (Finset.mem_insert_of_mem hw)⟩

lemma Y_eq_Ncount_singleton {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) :
    Y G u k t r = Ncount G {u} k t r := by
  classical
  unfold Y Ncount
  symm
  apply Finset.card_bij (fun W _ => insert u W)
  · intro W hW
    obtain ⟨_,hc,ha,ht⟩ := Finset.mem_filter.mp hW
    obtain ⟨hu,hr⟩ := (singleton_attached_iff G u W).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hr,?_,by simpa using ht⟩
    rw [Finset.card_insert_of_notMem hu,hc]
  · intro W hW Z hZ he
    have huW := ((singleton_attached_iff G u W).mp (Finset.mem_filter.mp hW).2.2.1).1
    have huZ := ((singleton_attached_iff G u Z).mp (Finset.mem_filter.mp hZ).2.2.1).1
    have hh := congrArg (fun A : Finset V => A.erase u) he
    simpa [Finset.erase_insert,Finset.erase_eq_of_notMem huW,Finset.erase_eq_of_notMem huZ] using hh
  · intro B hB
    obtain ⟨_,hr,hcard,ht⟩ := Finset.mem_filter.mp hB
    have he : insert u (B.erase u) = B := Finset.insert_erase hr.1
    refine ⟨B.erase u,?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,?_⟩
    · rw [Finset.card_erase_of_mem hr.1,hcard]
      omega
    · apply (singleton_attached_iff G u _).mpr
      exact ⟨Finset.notMem_erase _ _,by simpa only [he] using hr⟩
    · simpa [he] using ht
set_option autoImplicit false

lemma arrival_expansion_derivative (n : ℕ) (coeff : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z : ℝ => ∑ j ∈ Finset.range (n+1), coeff j * Real.exp (-(j:ℝ)*z))
      (-(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))) s := by
  have hd (j : ℕ) : HasDerivAt
      (fun z : ℝ => coeff j * Real.exp (-(j:ℝ)*z))
      (coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) s := by
    simpa using (((hasDerivAt_id s).const_mul (-(j:ℝ))).exp.const_mul (coeff j))
  have hh := HasDerivAt.fun_sum (u := Finset.range (n+1)) (fun j _ => hd j)
  have he : (∑ j ∈ Finset.range (n+1), coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) =
      -(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at hh
  exact hh

lemma derivative_from_arrival_expansion (f d : ℝ → ℝ) (n : ℕ) (coeff : ℕ → ℝ)
    (t : ℝ)
    (hf : ∀ s ∈ Set.Icc 0 t, f s = ∑ j ∈ Finset.range (n+1), coeff j*Real.exp (-(j:ℝ)*s))
    (hd : ∀ s ∈ Set.Icc 0 t, d s = ∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))
    (s : ℝ) (hs : s ∈ Set.Ico 0 t) : HasDerivWithinAt f (-d s) (Set.Icc 0 t) s := by
  have hs' : s ∈ Set.Icc 0 t := ⟨hs.1,hs.2.le⟩
  rw [hd s hs']
  exact (arrival_expansion_derivative n coeff s).hasDerivWithinAt.congr_of_mem hf hs'
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (Y G u k s r : ℝ))) ∧
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ))) ∧
    ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s' : ℝ => ∫ r, (Y G u k s' r : ℝ) ∂(rootLaw u ρ))
        (-(∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ))) (Set.Icc 0 t) s := by
  refine ⟨?_,?_,?_⟩
  · intro s
    have hm : Measurable (fun r : V → ℝ => Y G u k s r) := by
      simpa only [Y_eq_Ncount_singleton] using Ncount_measurable G {u} k s
    fun_prop
  · intro s
    have hm := dsSum_measurable G u k s
    fun_prop
  · obtain ⟨n,coeff,hf,hd⟩ := root_count_arrival_expansion G u k hk t ρ ht htρ
    exact derivative_from_arrival_expansion _ _ n coeff t hf hd


