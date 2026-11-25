-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_bound_bbfbf4b931ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:09.929882+00:00
-- url     : https://prove2.me/submissions/cbb21166-7730-44dc-9a56-848538c6c83b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_frame_gen_572f531e0883

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (B : ChartBundle ℤ x r E) {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (bb : Fin K → Fin r → E)
    (hli : ∀ l, LinearIndependent Ω (bb l)) (hsp : ∀ l, Submodule.span Ω (Set.range (bb l)) = ⊤)
    (hloc : ∀ l e, (∃ n : ℕ, f l ^ n • e ∈ B.lat i) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing ℤ x i) ∧ e = ∑ q, a q • bb l q)
    (l : Fin K) :
    ∃ M : ℕ, ∀ v ∈ B.lat i, ∀ q,
      f l ^ M * (Module.Basis.mk (hli l) (hsp l).ge).repr v q ∈ chartRing ℤ x i := by
  classical
  set Rg := chartRing ℤ x i
  let β : Fin K → Module.Basis (Fin r) Ω E := fun l => Module.Basis.mk (hli l) (hsp l).ge
  have hβ : ∀ l q, β l q = bb l q := fun l q => Module.Basis.mk_apply _ _ _
  have key : ∀ l, ∀ v ∈ B.lat i, ∀ q, ∃ n : ℕ, f l ^ n * (β l).repr v q ∈ Rg := by
    intro l v hv q
    obtain ⟨a, ha, hva⟩ := (hloc l v).1 ⟨0, by simpa using hv⟩
    have : (β l).repr v = a := by
      rw [hva]
      simp_rw [← hβ]
      exact (β l).repr_sum_self a
    rw [this]
    exact ha q
  choose nn hnn using fun l => frame_gen x i B (bb l) (hloc l)
  let g : Fin K × Fin r → E := fun p => f p.1 ^ nn p.1 p.2 • bb p.1 p.2
  let L : Submodule Rg E := Submodule.span Rg (Set.range g)
  have smulR : ∀ (a : Ω), a ∈ Rg → ∀ v : E, v ∈ L → a • v ∈ L := fun a ha v hv => by
    have := L.smul_mem (⟨a, ha⟩ : Rg) hv
    rwa [Subalgebra.smul_def] at this
  have loc : ∀ v ∈ B.lat i, ∀ l', ∃ T : ℕ, f l' ^ T • v ∈ L := by
    intro v hv l'
    obtain ⟨a, ha, hva⟩ := (hloc l' v).1 ⟨0, by simpa using hv⟩
    choose m hm using ha
    refine ⟨∑ q, (m q + nn l' q), ?_⟩
    rw [hva, Finset.smul_sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    have hle : m q + nn l' q ≤ ∑ q, (m q + nn l' q) :=
      Finset.single_le_sum (f := fun q => m q + nn l' q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have h2 : nn l' q ≤ ∑ q, (m q + nn l' q) := by omega
    have : f l' ^ (∑ q, (m q + nn l' q)) • a q • bb l' q =
        (f l' ^ (∑ q, (m q + nn l' q) - nn l' q) * a q) • g (l', q) := by
      simp only [g, smul_smul]
      congr 1
      rw [← pow_sub_mul_pow (f l') h2]
      ring
    rw [this]
    exact smulR _ (pow_mul_mem_of_le x i (hf l') (hm q) (by omega)) _ (Submodule.subset_span ⟨(l', q), rfl⟩)
  have cover : ∀ v ∈ B.lat i, v ∈ L := by
    intro v hv
    choose T hT using loc v hv
    obtain ⟨d, hd, hds⟩ := pu_pow x i f c hf hc hs (∑ l', T l')
    have hv' : v = ∑ l', d l' • (f l' ^ (∑ l', T l') • v) := by
      simp_rw [smul_smul, ← Finset.sum_smul, hds, one_smul]
    rw [hv']
    refine Submodule.sum_mem _ fun l' _ => smulR _ (hd l') _ ?_
    have hle : T l' ≤ ∑ l', T l' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l')
    rw [← pow_sub_mul_pow (f l') hle, mul_smul]
    exact smulR _ (pow_mem (hf l') _) _ (hT l')
  choose mg hmg using fun (p : Fin K × Fin r) q => key l (g p) (hnn p.1 p.2) q
  refine ⟨∑ p, ∑ q, mg p q, fun v hv q => ?_⟩
  have ind : ∀ y ∈ L, f l ^ (∑ p, ∑ q, mg p q) * (β l).repr y q ∈ Rg := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have h1 : mg p q ≤ ∑ q, mg p q :=
        Finset.single_le_sum (f := fun q => mg p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      have h2 : ∑ q, mg p q ≤ ∑ p, ∑ q, mg p q :=
        Finset.single_le_sum (f := fun p => ∑ q, mg p q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
      exact pow_mul_mem_of_le x i (hf l) (hmg p q) (h1.trans h2)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, Finsupp.add_apply, mul_add]
      exact add_mem hy hz
    | smul a y _ hy =>
      rw [Subalgebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem a.2 hy
  exact ind v (cover v hv)
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
