-- Prove2me | solution 1 for PadicMeasure.ext_of_residue_disk_masses
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:44:38.348462+00:00
-- url     : https://prove2.me/submissions/d44be7e6-d019-4da6-9619-d537385fb96f

import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.RingTheory.Coprime.Lemmas
import Theorems.Thm_ProfiniteMeasure_ext_of_clopen_masses

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace

local instance zmodTopology (m : ℕ) : TopologicalSpace (ZMod m) := ⊥
local instance zmodDiscrete (m : ℕ) : DiscreteTopology (ZMod m) := ⟨rfl⟩

private lemma reduction_continuous {p : ℕ} [Fact p.Prime] (n : ℕ) :
    Continuous (PadicInt.toZModPow n : ℤ_[p] → ZMod (p^n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply ContinuousAt.congr (f := fun _ => PadicInt.toZModPow n x) continuousAt_const
  have hpos : (0 : ℝ) < (p : ℝ)^(-n : ℤ) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
  symm
  apply sub_eq_zero.mp
  rw [← map_sub,← RingHom.mem_ker,PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact hy

namespace ColmezProof
open scoped BigOperators

private lemma unit_reduction_continuous {p : ℕ} [Fact p.Prime] (n : ℕ) :
    Continuous (fun x : (ℤ_[p])ˣ => PadicInt.toZModPow n x.val) :=
  (reduction_continuous n).comp Units.continuous_val

private lemma clopen_depth {p : ℕ} [Fact p.Prime] (U : Clopens (ℤ_[p])ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x y : (ℤ_[p])ˣ,
      PadicInt.toZModPow n x.val = PadicInt.toZModPow n y.val → (x ∈ U ↔ y ∈ U) := by
  classical
  let D (n : ℕ) : Set ((ℤ_[p])ˣ × (ℤ_[p])ˣ) :=
    {z | PadicInt.toZModPow n z.1.val ≠ PadicInt.toZModPow n z.2.val}
  have hDo (n : ℕ) : IsOpen (D n) :=
    (isClosed_eq ((unit_reduction_continuous n).comp continuous_fst)
      ((unit_reduction_continuous n).comp continuous_snd)).isOpen_compl
  have hK : IsCompact ((U : Set (ℤ_[p])ˣ) ×ˢ (U : Set (ℤ_[p])ˣ)ᶜ) :=
    U.isClosed.isCompact.prod U.isOpen.isClosed_compl.isCompact
  have hcover : ((U : Set (ℤ_[p])ˣ) ×ˢ (U : Set (ℤ_[p])ˣ)ᶜ) ⊆ ⋃ n, D n := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hne : x.val ≠ y.val := by
      intro hxy
      exact hy ((Units.val_injective hxy) ▸ hx)
    have hex : ∃ n, PadicInt.toZModPow n x.val ≠ PadicInt.toZModPow n y.val := by
      by_contra h
      push Not at h
      exact hne (PadicInt.ext_of_toZModPow.mp h)
    simpa only [mem_iUnion,D,mem_ofPred_eq] using hex
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover D hDo hcover
  let n := S.sup id + 1
  have hsep (x y : (ℤ_[p])ˣ) (hx : x ∈ U) (hy : y ∉ U) :
      PadicInt.toZModPow n x.val ≠ PadicInt.toZModPow n y.val := by
    intro he
    obtain ⟨m,hm,hxy⟩ := mem_iUnion₂.mp (hS (a := (x,y)) ⟨hx,hy⟩)
    have hmn : m ≤ n := (Finset.le_sup (f := id) hm).trans (Nat.le_succ _)
    have hem := congrArg (fun z : ZMod (p^n) => (ZMod.cast z : ZMod (p^m))) he
    rw [PadicInt.cast_toZModPow m n hmn,PadicInt.cast_toZModPow m n hmn] at hem
    exact hxy hem
  refine ⟨n,Nat.succ_pos _,fun x y hxy => ?_⟩
  constructor
  · intro hx
    by_contra hy
    exact hsep x y hx hy hxy
  · intro hy
    by_contra hx
    exact hsep y x hy hx hxy.symm

private def diskChar {p : ℕ} [Fact p.Prime] (n : ℕ) (a : ZMod (p^n)) :
    C((ℤ_[p])ˣ,ℂ_[p]) :=
  ⟨{x : (ℤ_[p])ˣ | PadicInt.toZModPow n x.val = a}.indicator (fun _ => 1),
    ((isClopen_discrete {a}).preimage (unit_reduction_continuous n)).continuous_indicator
      continuous_const⟩

private lemma diskChar_apply {p : ℕ} [Fact p.Prime] (n : ℕ) (a : ZMod (p^n))
    (x : (ℤ_[p])ˣ) : diskChar (p := p) n a x = if PadicInt.toZModPow n x.val = a then 1 else 0 := by
  change ({y : (ℤ_[p])ˣ | PadicInt.toZModPow n y.val = a}.indicator
    (fun _ => (1 : ℂ_[p]))) x = _
  by_cases h : PadicInt.toZModPow n x.val = a <;> simp [h]

private lemma measures_eq_of_disk_masses {p : ℕ} [Fact p.Prime]
    (μ ν : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p])
    (h : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      ∃ g : C((ℤ_[p])ˣ,ℂ_[p]),
        (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n)) then 1 else 0) ∧
        μ g = ν g) : μ = ν := by
  classical
  let : TotallyDisconnectedSpace (ℤ_[p])ˣ := ⟨isTotallyDisconnected_of_image
    Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  apply ProfiniteMeasure.ext_of_clopen_masses μ ν
  intro U
  obtain ⟨n,hn,hU⟩ := clopen_depth U
  have hmass (a : (ZMod (p^n))ˣ) : μ (diskChar (p := p) n a) = ν (diskChar (p := p) n a) := by
    have ha : IsCoprime (((a : ZMod (p^n)).val : ℕ) : ℤ) (p : ℤ) :=
      ((Nat.coprime_pow_right_iff hn _ _).mp (ZMod.val_coe_unit_coprime a)).isCoprime
    obtain ⟨g,hg,hmg⟩ := h n hn ((a : ZMod (p^n)).val : ℤ) ha
    have he : g = diskChar (p := p) n a := by
      ext x
      simpa only [diskChar_apply,Int.cast_natCast,ZMod.natCast_zmod_val] using hg x
    simpa only [he] using hmg
  let c (a : (ZMod (p^n))ˣ) : ℂ_[p] :=
    if ∃ x : (ℤ_[p])ˣ, x ∈ U ∧ PadicInt.toZModPow n x.val = (a : ZMod (p^n)) then 1 else 0
  let g := ∑ a : (ZMod (p^n))ˣ, c a • diskChar (p := p) n a
  have hg : g = ⟨(U : Set (ℤ_[p])ˣ).indicator (fun _ => (1 : ℂ_[p])),
      U.isClopen.continuous_indicator continuous_const⟩ := by
    ext x
    let b : (ZMod (p^n))ˣ := Units.map (PadicInt.toZModPow n).toMonoidHom x
    simp only [g,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,diskChar_apply]
    rw [Finset.sum_eq_single b]
    · have he : (∃ y : (ℤ_[p])ˣ, y ∈ U ∧
          PadicInt.toZModPow n y.val = (b : ZMod (p^n))) ↔ x ∈ U := by
        constructor
        · rintro ⟨y,hy,he⟩
          exact (hU y x he).mp hy
        · intro hx
          exact ⟨x,hx,rfl⟩
      have hb : PadicInt.toZModPow n x.val = (b : ZMod (p^n)) := rfl
      rw [if_pos hb,mul_one]
      change c b = (if x ∈ U then 1 else 0)
      simp only [c,he]
    · intro a _ hab
      have hne : PadicInt.toZModPow n x.val ≠ (a : ZMod (p^n)) := by
        intro he
        exact hab (Units.ext he.symm)
      simp [hne]
    · simp
  rw [← hg]
  simp only [g,map_sum,map_smul,hmass]

end ColmezProof

open ColmezProof in
theorem solution {p : ℕ} [Fact p.Prime]
    (μ ν : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p])
    (h : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      ∃ g : C((ℤ_[p])ˣ,ℂ_[p]),
        (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n)) then 1 else 0) ∧
        μ g = ν g) : μ = ν := by
  exact measures_eq_of_disk_masses μ ν h
