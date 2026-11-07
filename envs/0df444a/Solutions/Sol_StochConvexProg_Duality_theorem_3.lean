-- Prove2me | solution 1 for StochConvexProg.Duality.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:29:01.157282+00:00
-- url     : https://prove2.me/submissions/49801fdc-519b-4ed1-acc3-290dc59684cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual
import Theorems.Thm_StochConvexProg_Duality_proposition_3
import Theorems.Thm_StochConvexProg_Duality_compact_X0
import Theorems.Thm_StochConvexProg_Duality_eq_4_2
import Theorems.Thm_StochConvexProg_Duality_fenchel_moreau_U

open MeasureTheory

namespace SCPThm3Aux

/-- Infimum over a compact "support" of a jointly lsc function: attained and lsc. -/
theorem inf_attained_lsc {X U : Type*} [TopologicalSpace X] [TopologicalSpace U]
    (G : X × U → EReal) (K : Set X) (hK : IsCompact K) (hKne : K.Nonempty)
    (hG : LowerSemicontinuous G) (hsupp : ∀ x u, G (x, u) ≠ ⊤ → x ∈ K) :
    (∀ u, ∃ x, G (x, u) = ⨅ x', G (x', u)) ∧
      LowerSemicontinuous (fun u => ⨅ x, G (x, u)) := by
  have hatt : ∀ u, ∃ x, G (x, u) = ⨅ x', G (x', u) := by
    intro u
    have hlu : LowerSemicontinuous (fun x => G (x, u)) :=
      LowerSemicontinuous.comp (g := fun x => (x, u)) hG (Continuous.prodMk continuous_id continuous_const)
    obtain ⟨a, haK, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hKne hK (hlu.lowerSemicontinuousOn K)
    refine ⟨a, le_antisymm (le_iInf fun x' => ?_) (iInf_le _ _)⟩
    by_cases hx : x' ∈ K
    · exact hmin hx
    · have : G (x', u) = ⊤ := by
        by_contra h; exact hx (hsupp _ _ h)
      rw [this]; exact le_top
  refine ⟨hatt, ?_⟩
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha : a = ⊤
  · subst ha; simp
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ι : K × U → X × U := fun p => ((p.1 : X), p.2)
  have hι : Continuous ι := Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
    continuous_snd
  have hcl : IsClosed (ι ⁻¹' (G ⁻¹' Set.Iic a)) := (hG.isClosed_preimage a).preimage hι
  have himg := isClosedMap_snd_of_compactSpace _ hcl
  convert himg using 1
  ext u
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_image, Prod.exists]
  constructor
  · intro hu
    obtain ⟨x, hx⟩ := hatt u
    have hxa : G (x, u) ≤ a := hx ▸ hu
    have hxK : x ∈ K := hsupp x u (ne_top_of_le_ne_top ha hxa)
    exact ⟨⟨x, hxK⟩, u, hxa, rfl⟩
  · rintro ⟨x, u', hx, rfl⟩
    exact (iInf_le _ _).trans hx

/-- Convexity of the marginal function when the infimum is attained. -/
theorem econvex_marginal {X U : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup U]
    [Module ℝ U] (G : X × U → EReal)
    (hG : StochConvexProg.Duality.EConvex G)
    (hatt : ∀ u, ∃ x, G (x, u) = ⨅ x', G (x', u)) :
    StochConvexProg.Duality.EConvex (fun u => ⨅ x, G (x, u)) := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_setOf_eq] at hp hq ⊢
  obtain ⟨x₁, hx₁⟩ := hatt p.1
  obtain ⟨x₂, hx₂⟩ := hatt q.1
  have h1 : ((x₁, p.1), p.2) ∈ {r : (X × U) × ℝ | G r.1 ≤ (r.2 : EReal)} := by
    simp only [Set.mem_setOf_eq]; rw [hx₁]; exact hp
  have h2 : ((x₂, q.1), q.2) ∈ {r : (X × U) × ℝ | G r.1 ≤ (r.2 : EReal)} := by
    simp only [Set.mem_setOf_eq]; rw [hx₂]; exact hq
  have h3 := hG h1 h2 ha hb hab
  simp only [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk] at h3
  exact (iInf_le _ _).trans h3

end SCPThm3Aux

open StochConvexProg.Duality in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂)
    (hC₁ : Bornology.IsBounded pr.C₁) (hC₂ : Bornology.IsBounded pr.C₂) :
    (∃ x : XSpace σ n₁ n₂, pr.F x 0 = pr.infP) ∧ pr.infP = pr.supD ∧ ⊥ < pr.supD ∧
      EProper pr.phi ∧ EConvex pr.phi ∧
      @LowerSemicontinuous (USpace σ m₁ m₂) EReal (weakU σ m₁ m₂) _ pr.phi ∧
      (∀ u : USpace σ m₁ m₂, ∃ x : XSpace σ n₁ n₂, pr.F x u = pr.phi u) ∧
      biconjU pr.phi = pr.phi := by
  obtain ⟨hFconv, ⟨p₀, hp₀⟩, -, hFlsc⟩ := proposition_3 pr
  have hK := (compact_X0 pr hC₁ hC₂).1
  -- (4.15): `F(x, u) < +∞` implies `x ∈ X₀`
  have hsupp : ∀ (x : XSpace σ n₁ n₂) (u : USpace σ m₁ m₂),
      (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2) (x, u) ≠ ⊤ → x ∈ pr.X₀ := by
    intro x u h
    simp only [Problem.F] at h
    split_ifs at h with hfe
    · exact ⟨hfe.1, hfe.2.2.mono fun s hs => hs.1⟩
    · exact absurd rfl h
  have hKne : pr.X₀.Nonempty := ⟨p₀.1, hsupp p₀.1 p₀.2 hp₀⟩
  obtain ⟨hatt, hlsc⟩ := @SCPThm3Aux.inf_attained_lsc _ _ (weakX σ n₁ n₂) (weakU σ m₁ m₂)
    (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2) pr.X₀ hK hKne hFlsc hsupp
  have hatt' : ∀ u : USpace σ m₁ m₂, ∃ x : XSpace σ n₁ n₂, pr.F x u = pr.phi u := hatt
  have hFbot : ∀ x u, pr.F x u ≠ ⊥ := by
    intro x u
    simp only [Problem.F]
    split_ifs
    · exact EReal.coe_ne_bot _
    · exact top_ne_bot
  have hproper : EProper pr.phi := by
    refine ⟨fun u => ?_, p₀.2, ?_⟩
    · obtain ⟨x, hx⟩ := hatt' u
      rw [← hx]; exact hFbot x u
    · exact ne_top_of_le_ne_top hp₀ (iInf_le _ _)
  have hconv : EConvex pr.phi :=
    SCPThm3Aux.econvex_marginal (fun p : XSpace σ n₁ n₂ × USpace σ m₁ m₂ => pr.F p.1 p.2)
      hFconv hatt
  have hbic : biconjU pr.phi = pr.phi := fenchel_moreau_U pr.phi hproper hconv hlsc
  have h42 := eq_4_2 pr
  have hinf : pr.infP = pr.phi 0 := rfl
  have hsupD : pr.supD = pr.infP := by rw [← h42, hbic, hinf]
  refine ⟨hatt' 0, hsupD.symm, ?_, hproper, hconv, hlsc, hatt', hbic⟩
  rw [hsupD, hinf]
  exact bot_lt_iff_ne_bot.mpr (hproper.1 0)
