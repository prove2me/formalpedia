-- Prove2me | solution 1 for PadicMeasure.colmez_r0_moment_extension
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T06:12:20.918821+00:00
-- url     : https://prove2.me/submissions/4e68b6dd-61eb-45b0-95a9-d99948a665d0

import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.RingTheory.Coprime.Lemmas
import Theorems.Thm_ProfiniteMeasure_ext_of_clopen_masses
import Theorems.Thm_PadicMeasure_compatible_disk_values_vanish_of_decay

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

private lemma refinement_residue_unique {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a : ℤ) (x : ZMod (p^(n+1)))
    (hx : (x.cast : ZMod (p^n)) = (a : ZMod (p^n))) :
    ∃! b : Fin p, x = ((a + (b.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) := by
  have hp : p.Prime := Fact.out
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hcast : (a : ZMod (p^n)) = ((x.val : ℤ) : ZMod (p^n)) := by
    rw [Int.cast_natCast,ZMod.natCast_val]
    exact hx.symm
  obtain ⟨q,hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a (x.val : ℤ) (p^n)).mp hcast
  let b : Fin p := ⟨(q % (p : ℤ)).toNat,by
    have ht := Int.emod_lt_of_pos q hpZ
    have hnon := Int.emod_nonneg q (ne_of_gt hpZ)
    omega⟩
  have hb : (b.val : ℤ) = q % (p : ℤ) := by
    dsimp [b]
    exact Int.toNat_of_nonneg (Int.emod_nonneg q (ne_of_gt hpZ))
  have he : x = ((a + (b.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) := by
    rw [← ZMod.natCast_zmod_val x]
    suffices hdiv : ((p^(n+1) : ℕ) : ℤ) ∣ a + (b.val : ℤ)*(p : ℤ)^n - (x.val : ℤ) by
      have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (x.val : ℤ)
        (a + (b.val : ℤ)*(p : ℤ)^n) (p^(n+1))).mpr hdiv
      push_cast at hh ⊢
      exact hh
    refine ⟨-(q / (p : ℤ)),?_⟩
    push_cast at hq ⊢
    rw [hb,pow_succ (p : ℤ)]
    have hdiv := Int.emod_add_mul_ediv q (p : ℤ)
    linear_combination -hq + (p : ℤ)^n * hdiv
  refine ⟨b,he,?_⟩
  intro c hc
  have heq : ((a + (b.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) =
      ((a + (c.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) := he.symm.trans hc
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (a + (b.val : ℤ)*(p : ℤ)^n) (a + (c.val : ℤ)*(p : ℤ)^n) (p^(n+1))).mp
      (by push_cast at heq ⊢; exact heq)
  have hdp : (p : ℤ) ∣ (c.val : ℤ) - b.val := by
    obtain ⟨t,ht⟩ := hd
    refine ⟨t,?_⟩
    have hpn : (p : ℤ)^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    apply mul_left_cancel₀ hpn
    push_cast at ht
    rw [pow_succ (p : ℤ)] at ht
    linear_combination ht
  have hemod : (b.val : ZMod p) = (c.val : ZMod p) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (b.val : ℤ) (c.val : ℤ) p).mpr hdp
  have hval := congrArg ZMod.val hemod
  apply Fin.ext
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt b.isLt,Nat.mod_eq_of_lt c.isLt] using hval.symm

private def diskPoly {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ) :
    C((ℤ_[p])ˣ,ℂ_[p]) :=
  ⟨{x : (ℤ_[p])ˣ | PadicInt.toZModPow n x.val = (a : ZMod (p^n))}.indicator
    (fun x => (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]))^j),
    ((isClopen_discrete {(a : ZMod (p^n))}).preimage
      (unit_reduction_continuous n)).continuous_indicator (by fun_prop)⟩

private lemma diskPoly_apply {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ)
    (x : (ℤ_[p])ˣ) : diskPoly j n a x =
      if PadicInt.toZModPow n x.val = (a : ZMod (p^n))
      then (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]))^j else 0 := by
  change ({y : (ℤ_[p])ˣ | PadicInt.toZModPow n y.val = (a : ZMod (p^n))}.indicator
    (fun y => (algebraMap ℚ_[p] ℂ_[p] (y.val : ℚ_[p]))^j)) x = _
  by_cases h : PadicInt.toZModPow n x.val = (a : ZMod (p^n)) <;> simp [h]

private lemma diskPoly_refinement {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ) :
    (∑ b ∈ Finset.range p, diskPoly (p := p) j (n+1) (a+(b : ℤ)*(p : ℤ)^n)) =
      diskPoly (p := p) j n a := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  ext x
  simp only [ContinuousMap.sum_apply,diskPoly_apply]
  by_cases hx : PadicInt.toZModPow n x.val = (a : ZMod (p^n))
  · obtain ⟨b,hb,hbu⟩ := refinement_residue_unique n a (PadicInt.toZModPow (n+1) x.val)
      (by rwa [PadicInt.cast_toZModPow n (n+1) (Nat.le_succ n)])
    rw [Finset.sum_eq_single b]
    · simp only [hx,hb,ite_true]
    · intro c _ hcb
      have hc : PadicInt.toZModPow (n+1) x.val ≠
          ((a + (c.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) := fun hc => hcb (hbu c hc)
      simp only [hc,ite_false]
    · simp
  · simp only [hx,ite_false]
    apply Finset.sum_eq_zero
    intro b _
    have hb : PadicInt.toZModPow (n+1) x.val ≠
        ((a + (b.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) := by
      intro hb
      have hc := congrArg (fun z : ZMod (p^(n+1)) => (ZMod.cast z : ZMod (p^n))) hb
      rw [PadicInt.cast_toZModPow n (n+1) (Nat.le_succ n)] at hc
      have hm : (p : ZMod (p^n))^n = 0 := by rw [← Nat.cast_pow,ZMod.natCast_self]
      have hcast : (ZMod.cast ((a + (b.val : ℤ)*(p : ℤ)^n : ℤ) : ZMod (p^(n+1))) : ZMod (p^n)) =
          (a : ZMod (p^n)) := by
        have hd := ZMod.cast_intCast (R := ZMod (p^n)) (pow_dvd_pow p (Nat.le_succ n))
          (a+(b.val : ℤ)*(p : ℤ)^n)
        push_cast at hd
        simpa only [Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast,hm,mul_zero,add_zero] using hd
      exact hx (hc.trans hcast)
    simp only [hb,ite_false]

private def centeredDisk {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ) :
    C((ℤ_[p])ˣ,ℂ_[p]) :=
  ∑ t ∈ Finset.range (j+1), ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t)) •
    diskPoly (p := p) t n a

private lemma centeredDisk_apply {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ)
    (x : (ℤ_[p])ˣ) : centeredDisk j n a x =
      if PadicInt.toZModPow n x.val = (a : ZMod (p^n))
      then (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]) - (a : ℂ_[p]))^j else 0 := by
  classical
  simp only [centeredDisk,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul,diskPoly_apply]
  by_cases hx : PadicInt.toZModPow n x.val = (a : ZMod (p^n))
  · simp only [hx,ite_true]
    rw [sub_eq_add_neg,add_pow]
    apply Finset.sum_congr rfl
    intro t _
    ring
  · simp only [hx,ite_false,mul_zero,Finset.sum_const_zero]

private lemma norm_padic_complex_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ‖(p : ℂ_[p])^n‖ = (p : ℝ)^(-n : ℤ) := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p,← map_pow,norm_algebraMap']
  simp [zpow_neg,zpow_natCast]

private lemma coordinate_disk_bound {p : ℕ} [Fact p.Prime]
    (n : ℕ) (a : ℤ) (x : (ℤ_[p])ˣ)
    (hx : PadicInt.toZModPow n x.val = (a : ZMod (p^n))) :
    ‖algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]) - (a : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])^n‖ := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) a,← map_sub,norm_algebraMap',norm_padic_complex_pow]
  change ‖((x.val - (a : ℤ_[p]) : ℤ_[p]) : ℚ_[p])‖ ≤ _
  rw [PadicInt.padic_norm_e_of_padicInt,PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow,RingHom.mem_ker,map_sub,map_intCast,hx,sub_self]

private lemma centeredDisk_norm {p : ℕ} [Fact p.Prime] (j n : ℕ) (a : ℤ) :
    ‖centeredDisk (p := p) j n a‖ ≤ ‖(p : ℂ_[p])^(n*j)‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  rw [centeredDisk_apply]
  split_ifs with hx
  · rw [norm_pow]
    calc
      _ ≤ ‖(p : ℂ_[p])^n‖^j := pow_le_pow_left₀ (norm_nonneg _) (coordinate_disk_bound n a x hx) j
      _ = _ := by rw [← norm_pow,← pow_mul]
  · simpa only [norm_zero] using norm_nonneg ((p : ℂ_[p])^(n*j))

private lemma higher_moments_of_masses {p : ℕ} [Fact p.Prime] (d : ℕ)
    (M : ℕ → ℕ → ℤ → ℂ_[p])
    (hadd : ∀ j : ℕ, j ≤ d → ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, M j (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = M j n a)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      ∀ j : ℕ, j ≤ d → ‖∑ t ∈ Finset.range (j+1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a‖ ≤ C * ‖(p : ℂ_[p])^(n*j)‖)
    (μ : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p])
    (hμ : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      μ (diskPoly (p := p) 0 n a) = M 0 n a) :
    ∀ j : ℕ, j ≤ d → ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      μ (diskPoly (p := p) j n a) = M j n a := by
  let A : C((ℤ_[p])ˣ,ℂ_[p]) →L[ℂ_[p]] ℂ_[p] := μ
  let K := max C ‖A‖
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst j
      exact hμ
    have hDadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
        (∑ b ∈ Finset.range p, (M j (n+1) (a+(b : ℤ)*(p : ℤ)^n) -
          μ (diskPoly (p := p) j (n+1) (a+(b : ℤ)*(p : ℤ)^n)))) =
        M j n a - μ (diskPoly (p := p) j n a) := by
      intro n hn a ha
      rw [Finset.sum_sub_distrib,hadd j hj n hn a ha,← map_sum,diskPoly_refinement]
    have hDbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
        ‖M j n a - μ (diskPoly (p := p) j n a)‖ ≤ K * ‖(p : ℂ_[p])^(n*j)‖ := by
      intro n hn a ha
      let T := ∑ t ∈ Finset.range (j+1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a
      have he : T - μ (centeredDisk (p := p) j n a) =
          M j n a - μ (diskPoly (p := p) j n a) := by
        simp only [T,centeredDisk,map_sum,map_smul,smul_eq_mul,← Finset.sum_sub_distrib]
        rw [Finset.sum_range_succ]
        have hz : (∑ t ∈ Finset.range j,
            ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a -
              ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t)) * μ (diskPoly t n a))) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          rw [ih t (Finset.mem_range.mp ht) ((Nat.le_of_lt (Finset.mem_range.mp ht)).trans hj) n hn a ha,sub_self]
        rw [hz]
        simp only [zero_add,Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero]
      have hA : ‖μ (centeredDisk (p := p) j n a)‖ ≤ ‖A‖ * ‖(p : ℂ_[p])^(n*j)‖ :=
        (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (centeredDisk_norm j n a) (norm_nonneg A))
      rw [← he]
      have htri : ‖T - μ (centeredDisk (p := p) j n a)‖ ≤
          max ‖T‖ ‖μ (centeredDisk (p := p) j n a)‖ := by
        simpa only [sub_eq_add_neg,norm_neg] using
          IsUltrametricDist.norm_add_le_max T (-μ (centeredDisk (p := p) j n a))
      apply htri.trans
      apply max_le
      · exact (hbound n hn a ha j hj).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · exact hA.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hpNorm : ‖(p : ℂ_[p])‖ < 1 := by
      have hpEq : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
        simpa using norm_padic_complex_pow (p := p) 1
      rw [hpEq]
      exact (inv_lt_one₀ (by exact_mod_cast (Fact.out : p.Prime).pos)).mpr
        (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have hnj : Tendsto (fun n : ℕ => n*j) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hj0)) tendsto_id
    have hlim : Tendsto (fun n : ℕ => K * ‖(p : ℂ_[p])^(n*j)‖) atTop (nhds 0) := by
      have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℂ_[p])) hpNorm).comp hnj).const_mul K
      simpa only [mul_zero,norm_pow,Function.comp_apply] using ht
    have hv := PadicMeasure.compatible_disk_values_vanish_of_decay
      (fun n a => M j n a - μ (diskPoly (p := p) j n a)) hDadd
      (fun n => K * ‖(p : ℂ_[p])^(n*j)‖) hlim hDbound
    intro n hn a ha
    exact (sub_eq_zero.mp (hv n hn a ha)).symm

open UniformSpace ContinuousMap

/-- A bounded family stabilizing on clopen indicators determines an abstract measure. -/
private lemma exists_of_stabilization {X R : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [NormedField R] [CompleteSpace R]
    (L : ℕ → C(X,R) →L[R] R) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n f, ‖L n f‖ ≤ C * ‖f‖)
    (hstable : ∀ U : Clopens X, ∃ v : R, ∀ᶠ n : ℕ in atTop,
      L n ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩ = v) :
    ∃ μ : AbstractMeasure X R R,
      (∀ f : C(X,R), ∀ v : R, (∀ᶠ n : ℕ in atTop, L n f = v) → μ f = v) ∧
      (∀ f : C(X,R), ‖μ f‖ ≤ C * ‖f‖) := by
  classical
  let E : Submodule R C(X,R) := {
    carrier := {f | ∃ v : R, ∀ᶠ n : ℕ in atTop, L n f = v}
    zero_mem' := ⟨0,by simp⟩
    add_mem' := by
      rintro f g ⟨v,hv⟩ ⟨w,hw⟩
      refine ⟨v+w,?_⟩
      filter_upwards [hv,hw] with n hn hm
      simp only [map_add,hn,hm]
    smul_mem' := by
      rintro a f ⟨v,hv⟩
      refine ⟨a*v,?_⟩
      filter_upwards [hv] with n hn
      simp only [map_smul,hn,smul_eq_mul] }
  let ev (f : E) : R := Classical.choose f.property
  have hev (f : E) : ∀ᶠ n : ℕ in atTop, L n f.val = ev f :=
    Classical.choose_spec f.property
  let F : E →ₗ[R] R := {
    toFun := ev
    map_add' := by
      intro f g
      obtain ⟨n,hn,hm,hs⟩ := ((hev f).and ((hev g).and (hev (f+g)))).exists
      change L n (f.val+g.val) = ev (f+g) at hs
      rw [map_add,hn,hm] at hs
      exact hs.symm
    map_smul' := by
      intro a f
      obtain ⟨n,hn,hs⟩ := ((hev f).and (hev (a • f))).exists
      change L n (a • f.val) = ev (a • f) at hs
      rw [map_smul,hn] at hs
      exact hs.symm }
  have hFbound (f : E) : ‖F f‖ ≤ C * ‖E.subtype f‖ := by
    obtain ⟨n,hn⟩ := (hev f).exists
    change ‖ev f‖ ≤ C * ‖f.val‖
    rw [← hn]
    exact hbound n f.val
  have hdense : DenseRange E.subtype := by
    intro f
    simp_rw [mem_closure_iff,Set.nonempty_def]
    intro W hWo hWf
    have hW := mem_nhds_uniformity_iff_right.mp (hWo.mem_nhds hWf)
    obtain ⟨J,hJ,hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp hW
    obtain ⟨n,U,v,hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
      f (nhdsSet_diagonal_le_uniformity hJ)
    let e (i : Fin n) : C(X,R) :=
      ⟨(U i : Set X).indicator (fun _ => (1 : R)),
        (U i).isClopen.continuous_indicator continuous_const⟩
    let g := ∑ i : Fin n, v i • e i
    have hge : g ∈ E := by
      apply E.sum_mem
      intro i _
      exact E.smul_mem (v i) (hstable (U i))
    have hgp (x : X) : g x = ∑ i : Fin n, (U i : Set X).indicator (fun _ => v i) x := by
      simp only [g,ContinuousMap.sum_apply,ContinuousMap.smul_apply,e,
        ContinuousMap.coe_mk,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hx : x ∈ U i <;> simp [hx]
    have hG := Set.mem_of_subset_of_mem hJ' (a := (f,g))
    simp only [Set.mem_ofPred_eq,forall_const] at hG
    exact ⟨g,hG (by simpa only [hgp] using hv),⟨⟨g,hge⟩,rfl⟩⟩
  let μ : AbstractMeasure X R R := F.extendOfNorm E.subtype
  refine ⟨μ,?_,?_⟩
  · intro f v hv
    let x : E := ⟨f,⟨v,hv⟩⟩
    have hx := LinearMap.extendOfNorm_eq (f := F) (e := E.subtype) hdense ⟨C,hFbound⟩ x
    change μ f = ev x at hx
    obtain ⟨n,hn,hm⟩ := ((hev x).and hv).exists
    exact hx.trans (hn.symm.trans hm)
  · intro f
    exact LinearMap.norm_extendOfNorm_apply_le hdense C hFbound f

private def intSample {p : ℕ} [Fact p.Prime] (a : ℤ) : (ℤ_[p])ˣ :=
  if ha : IsCoprime a (p : ℤ) then
    (PadicInt.isUnit_iff.mpr (PadicInt.norm_intCast_eq_one_iff.mpr ha)).unit else 1

private lemma intSample_val {p : ℕ} [Fact p.Prime] (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) : (intSample (p := p) a).val = (a : ℤ_[p]) := by
  simp only [intSample,dif_pos ha,IsUnit.unit_spec]

private lemma sum_range_product {R : Type*} [AddCommMonoid R] (q r : ℕ) (f : ℕ → R) :
    (∑ a ∈ Finset.range (q*r), f a) =
      ∑ a ∈ Finset.range q, ∑ b ∈ Finset.range r, f (a+b*q) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih]
    simp_rw [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring

private lemma coprime_child_iff {p : ℕ} (n : ℕ) (hn : 0 < n) (a b : ℤ) :
    IsCoprime (a+b*(p : ℤ)^n) (p : ℤ) ↔ IsCoprime a (p : ℤ) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [pow_succ,mul_assoc] using
    (IsCoprime.add_mul_right_left_iff (x := a) (y := (p : ℤ)) (z := b*(p : ℤ)^r))

private def approxCLM {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p]) (n : ℕ) :
    C((ℤ_[p])ˣ,ℂ_[p]) →L[ℂ_[p]] ℂ_[p] :=
  ∑ a ∈ Finset.range (p^n), if IsCoprime (a : ℤ) (p : ℤ) then
    m n a • ContinuousMap.evalCLM ℂ_[p] (intSample (p := p) a) else 0

private lemma approxCLM_apply {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (n : ℕ) (f : C((ℤ_[p])ˣ,ℂ_[p])) :
    approxCLM m n f = ∑ a ∈ Finset.range (p^n), if IsCoprime (a : ℤ) (p : ℤ)
      then m n a * f (intSample (p := p) a) else 0 := by
  classical
  simp only [approxCLM,_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

private lemma approxCLM_bound {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖m n a‖ ≤ C)
    (n : ℕ) (hn : 0 < n) (f : C((ℤ_[p])ˣ,ℂ_[p])) :
    ‖approxCLM m n f‖ ≤ C * ‖f‖ := by
  rw [approxCLM_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
    (Finset.nonempty_range_iff.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero))
  intro a _
  split_ifs with ha
  · rw [norm_mul]
    exact mul_le_mul (hm n hn a ha) (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) hC
  · simpa only [norm_zero] using mul_nonneg hC (norm_nonneg f)

private lemma approxCLM_refinement {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, m (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = m n a)
    (n : ℕ) (hn : 0 < n) (f : C((ℤ_[p])ˣ,ℂ_[p]))
    (hf : ∀ x y : (ℤ_[p])ˣ, PadicInt.toZModPow n x.val = PadicInt.toZModPow n y.val → f x = f y) :
    approxCLM m (n+1) f = approxCLM m n f := by
  classical
  rw [approxCLM_apply,approxCLM_apply,pow_succ,sum_range_product]
  apply Finset.sum_congr rfl
  intro a _
  have hc (b : ℕ) : IsCoprime ((a+b*p^n : ℕ) : ℤ) (p : ℤ) ↔ IsCoprime (a : ℤ) (p : ℤ) := by
    push_cast
    exact coprime_child_iff n hn a b
  by_cases ha : IsCoprime (a : ℤ) (p : ℤ)
  · simp only [hc,ha,ite_true]
    have he (b : ℕ) : f (intSample (p := p) ((a+b*p^n : ℕ) : ℤ)) = f (intSample (p := p) a) := by
      apply hf
      rw [intSample_val _ ((hc b).mpr ha),intSample_val _ ha]
      simp only [map_intCast]
      push_cast
      rw [← Nat.cast_pow,ZMod.natCast_self,mul_zero,add_zero]
    simp_rw [he]
    rw [← Finset.sum_mul]
    congr 1
    convert hadd n hn a ha using 1
    push_cast
    rfl
  · simp only [hc,ha,ite_false,Finset.sum_const_zero]

private lemma approxCLM_stable {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, m (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = m n a)
    (k : ℕ) (hk : 0 < k) (f : C((ℤ_[p])ˣ,ℂ_[p]))
    (hf : ∀ x y : (ℤ_[p])ˣ, PadicInt.toZModPow k x.val = PadicInt.toZModPow k y.val → f x = f y) :
    ∀ n : ℕ, k ≤ n → approxCLM m n f = approxCLM m k f := by
  intro n hkn
  induction n,hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    rw [approxCLM_refinement m hadd n (hk.trans_le hkn) f,ih]
    intro x y hxy
    apply hf
    have he := congrArg (fun z : ZMod (p^n) => (ZMod.cast z : ZMod (p^k))) hxy
    rwa [PadicInt.cast_toZModPow k n hkn,PadicInt.cast_toZModPow k n hkn] at he

private lemma approxCLM_disk {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (hres : ∀ n : ℕ, 0 < n → ∀ a b : ℤ, IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) → m n a = m n b)
    (n : ℕ) (hn : 0 < n) (a : ℤ) (ha : IsCoprime a (p : ℤ)) :
    approxCLM m n (diskPoly (p := p) 0 n a) = m n a := by
  classical
  let r := (a : ZMod (p^n)).val
  have hrlt : r < p^n := ZMod.val_lt _
  let u : (ZMod (p^n))ˣ := ZMod.unitOfIsCoprime a (by simpa only [Nat.cast_pow] using (ha.pow_right (n := n)))
  have hr : IsCoprime (r : ℤ) (p : ℤ) :=
    ((Nat.coprime_pow_right_iff hn _ _).mp (ZMod.val_coe_unit_coprime u)).isCoprime
  have hre : (r : ZMod (p^n)) = (a : ZMod (p^n)) := ZMod.natCast_zmod_val _
  have hrm : m n r = m n a := hres n hn r a hr ha (by simpa only [Int.cast_natCast] using hre)
  rw [approxCLM_apply,Finset.sum_eq_single r]
  · rw [if_pos hr,diskPoly_apply,intSample_val _ hr,map_intCast,Int.cast_natCast,if_pos hre]
    simpa only [pow_zero,mul_one] using hrm
  · intro b hb hbr
    by_cases hbc : IsCoprime (b : ℤ) (p : ℤ)
    · rw [if_pos hbc,diskPoly_apply,intSample_val _ hbc,map_intCast,Int.cast_natCast]
      have hne : (b : ZMod (p^n)) ≠ (a : ZMod (p^n)) := by
        intro he
        have hv := congrArg ZMod.val he
        exact hbr (by simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using hv)
      simp only [hne,ite_false,mul_zero]
    · simp only [hbc,ite_false]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hrlt))

private lemma measure_of_masses {p : ℕ} [Fact p.Prime] (m : ℕ → ℤ → ℂ_[p])
    (hres : ∀ n : ℕ, 0 < n → ∀ a b : ℤ, IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) → m n a = m n b)
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, m (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = m n a)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖m n a‖ ≤ C) :
    ∃ μ : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p],
      ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
        μ (diskPoly (p := p) 0 n a) = m n a := by
  classical
  let : TotallyDisconnectedSpace (ℤ_[p])ˣ := ⟨isTotallyDisconnected_of_image
    Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let L (n : ℕ) := approxCLM m (n+1)
  have hLbound (n : ℕ) (f : C((ℤ_[p])ˣ,ℂ_[p])) : ‖L n f‖ ≤ C * ‖f‖ :=
    approxCLM_bound m C hC hbound (n+1) (Nat.succ_pos _) f
  have hLstable (U : Clopens (ℤ_[p])ˣ) : ∃ v : ℂ_[p], ∀ᶠ n : ℕ in atTop,
      L n ⟨(U : Set (ℤ_[p])ˣ).indicator (fun _ => (1 : ℂ_[p])),
        U.isClopen.continuous_indicator continuous_const⟩ = v := by
    obtain ⟨k,hk,hU⟩ := clopen_depth U
    let f : C((ℤ_[p])ˣ,ℂ_[p]) := ⟨(U : Set (ℤ_[p])ˣ).indicator (fun _ => (1 : ℂ_[p])),
      U.isClopen.continuous_indicator continuous_const⟩
    have hf (x y : (ℤ_[p])ˣ) (hxy : PadicInt.toZModPow k x.val = PadicInt.toZModPow k y.val) :
        f x = f y := by
      change (if x ∈ U then 1 else 0) = (if y ∈ U then 1 else 0)
      simp only [hU x y hxy]
    refine ⟨approxCLM m k f,eventually_atTop.mpr ⟨k,fun n hkn => ?_⟩⟩
    exact approxCLM_stable m hadd k hk f hf (n+1) (hkn.trans (Nat.le_succ n))
  obtain ⟨μ,hμ,_⟩ := exists_of_stabilization L C hC hLbound hLstable
  refine ⟨μ,fun n hn a ha => ?_⟩
  apply hμ
  refine eventually_atTop.mpr ⟨n,fun r hnr => ?_⟩
  change approxCLM m (r+1) (diskPoly 0 n a) = m n a
  rw [approxCLM_stable m hadd n hn (diskPoly 0 n a) ?_ (r+1) (hnr.trans (Nat.le_succ r)),
    approxCLM_disk m hres n hn a ha]
  intro x y hxy
  simp only [diskPoly_apply,pow_zero,hxy]

end ColmezProof

open ColmezProof
open scoped BigOperators

theorem solution
    {p : ℕ} [Fact p.Prime] (d : ℕ)
    (M : ℕ → ℕ → ℤ → ℂ_[p])
    (hres : ∀ (n : ℕ), 0 < n → ∀ (a b : ℤ),
      IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) → M 0 n a = M 0 n b)
    (hadd : ∀ (j : ℕ), j ≤ d → ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        (∑ b ∈ Finset.range p, M j (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = M j n a)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) → ∀ (j : ℕ), j ≤ d →
        ‖∑ t ∈ Finset.range (j+1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a‖ ≤
          C * ‖(p : ℂ_[p])^(n*j)‖) :
    ∃! μ : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p],
      ∀ (n : ℕ), 0 < n → ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        ∀ (j : ℕ), j ≤ d → ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
          (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n))
            then (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]))^j else 0) ∧
          μ g = M j n a := by
  classical
  obtain ⟨C,hC,hbound⟩ := hbound
  have hzero : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖M 0 n a‖ ≤ C := by
    intro n hn a ha
    simpa using hbound n hn a ha 0 (Nat.zero_le d)
  obtain ⟨μ,hμ⟩ := measure_of_masses (M 0) hres (hadd 0 (Nat.zero_le d)) C hC hzero
  have hall := higher_moments_of_masses d M hadd C hC hbound μ hμ
  refine ⟨μ,?_,?_⟩
  · intro n hn a ha j hj
    exact ⟨diskPoly j n a,diskPoly_apply j n a,hall j hj n hn a ha⟩
  · intro ν hν
    apply measures_eq_of_disk_masses ν μ
    intro n hn a ha
    refine ⟨diskPoly 0 n a,?_,?_⟩
    · intro x
      simp only [diskPoly_apply,pow_zero]
    · obtain ⟨g,hg,hνg⟩ := hν n hn a ha 0 (Nat.zero_le d)
      have he : g = diskPoly (p := p) 0 n a := by
        ext x
        exact (hg x).trans (diskPoly_apply 0 n a x).symm
      rw [he] at hνg
      exact hνg.trans (hμ n hn a ha).symm
