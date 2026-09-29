-- Prove2me | solution 1 for ResidualGaloisRep.exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/753b8c58-c84c-5f53-a14b-deb302b9ac73

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "IsIrreducible baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ mk"
namespace NonEisenstein
p2m_open "ResidualGaloisRep"

section Characters

variable {N : Type} [Group N] {K : Type} [Field K]

theorem pair_eq_of_add_eq_add (h2 : (2 : K) ≠ 0) (a b c d : N →* K)
    (h : ∀ n, a n + b n = c n + d n) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hli := linearIndependent_monoidHom N K

  let s : Finset (N →* K) := {a, b, c, d}
  let w : (N →* K) → K := fun f =>
    (if a = f then 1 else 0) + (if b = f then 1 else 0) - (if c = f then 1 else 0) - (if d = f then 1 else 0)
  have ha : a ∈ s := by simp [s]
  have hb : b ∈ s := by simp [s]
  have hc : c ∈ s := by simp [s]
  have hd : d ∈ s := by simp [s]
  have hsum : ∑ f ∈ s, w f • ((f : N →* K) : N → K) = 0 := by
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, w, add_mul, sub_mul, ite_mul,
      one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos ha,
      if_pos hb, if_pos hc, if_pos hd]
    rw [h n]; ring
  have hw : ∀ f ∈ s, w f = 0 := linearIndependent_iff'.mp hli s w hsum

  have hwa := hw a ha
  have hwb := hw b hb
  simp only [w, if_pos rfl] at hwa hwb
  by_cases hca : c = a
  · subst hca
    left
    refine ⟨rfl, ?_⟩
    by_contra hbd
    have hdb : ¬ d = b := fun h' => hbd h'.symm
    by_cases hab : c = b
    · subst hab
      simp only [if_pos rfl, if_neg hdb] at hwb
      norm_num at hwb
    · simp only [if_neg hab, if_neg hdb] at hwb
      norm_num at hwb
  · by_cases hda : d = a
    · subst hda
      right
      refine ⟨rfl, ?_⟩
      by_contra hbc
      have hcb : ¬ c = b := fun h' => hbc h'.symm
      by_cases hab : d = b
      · subst hab
        simp only [if_pos rfl, if_neg hcb] at hwb
        norm_num at hwb
      · simp only [if_neg hab, if_neg hcb] at hwb
        norm_num at hwb
    · exfalso
      simp only [if_neg hca, if_neg hda] at hwa
      by_cases hba : b = a
      · simp only [if_pos hba] at hwa
        apply h2
        rw [← hwa]; norm_num
      · simp only [if_neg hba] at hwa
        norm_num at hwa

end Characters

section Clifford

variable {K : Type} [Field K] [IsAlgClosed K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {G : Type} [Group G]

theorem false_of_line (ρ : G →* Module.End K V) (h2V : Module.finrank K V = 2)
    (hirr : ∀ W : Submodule K V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : V) (hv : v ≠ 0) (hst : ∀ g, ∃ c : K, ρ g v = c • v) : False := by
  have hW := hirr (K ∙ v) (fun g x hx => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, hc⟩ := hst g
    rw [map_smul, hc, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨a * c, rfl⟩)
  rcases hW with h | h
  · exact hv ((Submodule.span_singleton_eq_bot).mp h)
  · have := finrank_span_singleton (K := K) hv
    rw [h, finrank_top, h2V] at this
    norm_num at this

theorem exists_common_eigenvector (ρ : G →* Module.End K V) (h2V : Module.finrank K V = 2)
    (hcomm : ∀ g h, ρ g * ρ h = ρ h * ρ g) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ∃ c : K, ρ g v = c • v := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [h2V]; norm_num)
  by_cases hsc : ∀ g, ∃ c : K, ρ g = c • 1
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun g => ?_⟩
    obtain ⟨c, hc⟩ := hsc g
    exact ⟨c, by rw [hc]; rfl⟩
  · push Not at hsc
    obtain ⟨g₀, hg₀⟩ := hsc
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ g₀)
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine ⟨v, hv.2, fun g => ?_⟩

    set E := (ρ g₀).eigenspace μ with hE
    have hvE : v ∈ E := hv.1
    have hgE : ρ g v ∈ E := by
      rw [hE, Module.End.mem_eigenspace_iff] at hvE ⊢
      have := congrArg (fun f : Module.End K V => f v) (hcomm g₀ g)
      simp only [Module.End.mul_apply] at this
      rw [this, hvE, map_smul]

    have hEtop : E ≠ ⊤ := by
      intro htop
      apply hg₀ μ
      ext x
      have hx : x ∈ E := by rw [htop]; exact Submodule.mem_top
      rw [hE, Module.End.mem_eigenspace_iff] at hx
      rw [hx]; rfl
    have hE1 : Module.finrank K E = 1 := by
      have hle : Module.finrank K E ≤ 2 := h2V ▸ Submodule.finrank_le E
      have hlt : Module.finrank K E < 2 := by
        refine lt_of_le_of_ne hle fun h => hEtop ?_
        exact Submodule.eq_top_of_finrank_eq (h.trans h2V.symm)
      have hpos : 0 < Module.finrank K E := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        exact ⟨⟨v, hvE⟩, fun h => hv.2 (congrArg Subtype.val h)⟩
      omega

    have hEeq : E = K ∙ v := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact (Submodule.span_singleton_le_iff_mem v E).mpr hvE
      · rw [finrank_span_singleton hv.2, hE1]
    rw [hEeq] at hgE
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgE
    exact ⟨c, hc.symm⟩

omit [IsAlgClosed K] in

theorem eq_zero_of_forall_trace_mul_eq_zero (z : Module.End K V)
    (h : ∀ x : Module.End K V, LinearMap.trace K V (x * z) = 0) : z = 0 := by
  classical
  let b := Module.finBasis K V
  have key : LinearMap.toMatrix b b z = 0 := by
    refine (Matrix.ext_iff_trace_mul_left).mpr fun x => ?_
    rw [Matrix.mul_zero, Matrix.trace_zero]
    have := h (Matrix.toLin b b x)
    rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.toMatrix_mul, LinearMap.toMatrix_toLin] at this
    exact this
  exact (LinearEquiv.map_eq_zero_iff (LinearMap.toMatrix b b)).mp key

theorem false_of_trace_eq_one_add (h2 : (2 : K) ≠ 0)
    (ρ : G →* Module.End K V) (h2V : Module.finrank K V = 2)
    (hirr : ∀ W : Submodule K V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (N : Subgroup G) [N.Normal] (hcommN : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N)
    (ψ : G →* Kˣ) (htr : ∀ n ∈ N, LinearMap.trace K V (ρ n) = 1 + (ψ n : K)) : False := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [h2V]; norm_num)

  let ψN : ↥N →* K := (Units.coeHom K).comp (ψ.comp N.subtype)
  have hψN : ∀ n : ↥N, ψN n = (ψ (n : G) : K) := fun n => rfl
  by_cases hline : ∃ v : V, v ≠ 0 ∧ ∀ n ∈ N, ∃ c : K, ρ n v = c • v
  ·
    obtain ⟨v, hv, hev⟩ := hline

    have hχ : ∀ n : ↥N, ∃ c : K, ρ (n : G) v = c • v := fun n => hev n n.2
    choose χf hχf using hχ
    have hχmul : ∀ m n : ↥N, χf (m * n) = χf m * χf n := by
      intro m n
      have h1 : ρ ((m * n : ↥N) : G) v = (χf m * χf n) • v := by
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hχf n, map_smul, hχf m, smul_smul,
          mul_comm]
      rw [hχf (m * n)] at h1
      exact smul_left_injective K hv h1
    have hχone : χf 1 = 1 := by
      have h1 := hχf 1
      rw [Subgroup.coe_one, map_one, Module.End.one_apply] at h1
      have h1' : (fun c : K => c • v) 1 = (fun c : K => c • v) (χf 1) := by
        simp only [one_smul]; exact h1
      exact (smul_left_injective K hv h1').symm
    let χ : ↥N →* K := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
    have hχv : ∀ n : ↥N, ρ (n : G) v = χ n • v := hχf

    by_cases hGst : ∀ g : G, ∃ c : K, ρ g v = c • v
    · exact false_of_line ρ h2V hirr v hv hGst
    push Not at hGst
    obtain ⟨g₀, hg₀⟩ := hGst
    set w := ρ g₀ v with hw

    have hvw : LinearIndependent K ![v, w] := by
      refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
      by_contra hne
      have ht : t ≠ 0 := by
        intro ht
        rw [ht, zero_smul, add_zero] at hst
        exact hne ⟨smul_eq_zero.mp hst |>.resolve_right hv, ht⟩
      apply hg₀ (-(s / t))
      have : t • w = -(s • v) := eq_neg_of_add_eq_zero_right hst
      calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = -(s / t) • v := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

    let cg : ↥N →* ↥N :=
      { toFun := fun n => ⟨g₀⁻¹ * n * g₀, by
          have := Subgroup.Normal.conj_mem inferInstance (n : G) n.2 g₀⁻¹
          rwa [inv_inv] at this⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun m n => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hcg : ∀ n : ↥N, ((cg n : ↥N) : G) = g₀⁻¹ * n * g₀ := fun n => rfl
    let χ' : ↥N →* K := χ.comp cg
    have hχ'app : ∀ n : ↥N, χ' n = χ (cg n) := fun n => rfl
    have hχ'w : ∀ n : ↥N, ρ (n : G) w = χ' n • w := by
      intro n
      have : (n : G) = g₀ * (g₀⁻¹ * n * g₀) * g₀⁻¹ := by group
      rw [hw, ← Module.End.mul_apply, ← map_mul, this, mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
        map_mul, Module.End.mul_apply, ← hcg, hχv (cg n), map_smul]
      rfl

    let bvw : Module.Basis (Fin 2) K V :=
      basisOfLinearIndependentOfCardEqFinrank hvw (by rw [h2V]; rfl)
    have hbcoe : ⇑bvw = ![v, w] := coe_basisOfLinearIndependentOfCardEqFinrank hvw _
    have hb0 : bvw 0 = v := by rw [hbcoe]; rfl
    have hb1 : bvw 1 = w := by rw [hbcoe]; rfl
    have htrN : ∀ n : ↥N, LinearMap.trace K V (ρ (n : G)) = χ n + χ' n := by
      intro n
      rw [LinearMap.trace_eq_matrix_trace K bvw, Matrix.trace_fin_two]
      have h00 : LinearMap.toMatrix bvw bvw (ρ (n : G)) 0 0 = χ n := by
        rw [LinearMap.toMatrix_apply, hb0, hχv n, ← hb0, map_smul, Finsupp.smul_apply, bvw.repr_self,
          Finsupp.single_eq_same, smul_eq_mul, mul_one]
      have h11 : LinearMap.toMatrix bvw bvw (ρ (n : G)) 1 1 = χ' n := by
        rw [LinearMap.toMatrix_apply, hb1, hχ'w n, ← hb1, map_smul, Finsupp.smul_apply, bvw.repr_self,
          Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [h00, h11]
    have hsum : ∀ n : ↥N, χ n + χ' n = (1 : ↥N →* K) n + ψN n := by
      intro n
      rw [← htrN n, htr n n.2, MonoidHom.one_apply, hψN]

    have hψinv : ∀ n : ↥N, ψN (cg n) = ψN n := by
      intro n
      rw [hψN, hψN, hcg, map_mul, map_mul, Units.val_mul, Units.val_mul, mul_comm ((ψ g₀⁻¹ : Kˣ) : K) _,
        mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
    have hχχ' : χ' = χ ∧ χ = 1 := by
      rcases pair_eq_of_add_eq_add h2 χ χ' 1 ψN hsum with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      ·
        have hχ'1 : χ' = 1 := by
          ext n; rw [hχ'app, hc1]; rfl
        exact ⟨hχ'1.trans hc1.symm, hc1⟩
      ·
        have hχ'ψ : χ' = ψN := by
          ext n; rw [hχ'app, hc1]; exact hψinv n
        have h1ψ : ψN = 1 := hχ'ψ.symm.trans hc2
        exact ⟨hχ'ψ.trans hc1.symm, hc1.trans h1ψ⟩
    obtain ⟨hχ'χ, hχ1⟩ := hχχ'

    have hNtriv : ∀ n : ↥N, ρ (n : G) = 1 := by
      intro n
      refine bvw.ext fun i => ?_
      fin_cases i
      · change ρ (n : G) (bvw 0) = bvw 0
        rw [hb0, hχv n, hχ1, MonoidHom.one_apply, one_smul]
      · change ρ (n : G) (bvw 1) = bvw 1
        rw [hb1, hχ'w n, hχ'χ, hχ1, MonoidHom.one_apply, one_smul]

    have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
      intro a b
      have h1 : ρ (a * b * a⁻¹ * b⁻¹) = 1 := hNtriv ⟨_, hcommN a b⟩
      have : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      rw [← map_mul, ← map_mul, this, map_mul, h1, one_mul]
    obtain ⟨u, hu, hust⟩ := exists_common_eigenvector ρ h2V hcomm
    exact false_of_line ρ h2V hirr u hu hust
  ·
    let ρN : Representation K ↥N V := ρ.comp N.subtype
    have hρN : ∀ n : ↥N, ρN n = ρ (n : G) := fun n => rfl

    have hbot : ∀ W : Subrepresentation ρN, W.toSubmodule = ⊥ → W = ⊥ := fun W h =>
      Subrepresentation.toSubmodule_injective h
    have htop : ∀ W : Subrepresentation ρN, W.toSubmodule = ⊤ → W = ⊤ := fun W h =>
      Subrepresentation.toSubmodule_injective h
    have hnt : Nontrivial (Subrepresentation ρN) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      have h' : ((⊥ : Subrepresentation ρN).toSubmodule) = (⊤ : Subrepresentation ρN).toSubmodule := by
        rw [h]
      change (⊥ : Submodule K V) = ⊤ at h'
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have : x ∈ (⊥ : Submodule K V) := by rw [h']; exact Submodule.mem_top
      exact hx ((Submodule.mem_bot K).mp this)
    have hW : ∀ W : Subrepresentation ρN, W = ⊥ ∨ W = ⊤ := by
      intro W
      have hle : Module.finrank K W.toSubmodule ≤ 2 := h2V ▸ Submodule.finrank_le W.toSubmodule
      rcases Nat.lt_or_ge (Module.finrank K W.toSubmodule) 1 with h0 | h1
      · left
        apply hbot
        exact Submodule.finrank_eq_zero.mp (by omega)
      rcases Nat.lt_or_ge (Module.finrank K W.toSubmodule) 2 with h1' | h2'
      · exfalso
        have hW1 : Module.finrank K W.toSubmodule = 1 := by omega
        obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.mp hW1
        refine hline ⟨(v : V), fun h => hv0 (Subtype.ext h), fun n hn => ?_⟩
        have hmem : ρ n (v : V) ∈ W.toSubmodule := W.apply_mem_toSubmodule ⟨n, hn⟩ v.2
        obtain ⟨c, hc⟩ := hvspan ⟨ρ n (v : V), hmem⟩
        exact ⟨c, (congrArg Subtype.val hc).symm⟩
      · right
        apply htop
        exact Submodule.eq_top_of_finrank_eq ((le_antisymm hle h2').trans h2V.symm)
    haveI : ρN.IsIrreducible := @IsSimpleOrder.mk _ _ _ hnt hW
    have hspanN : Submodule.span K (Set.range ⇑ρN) = ⊤ :=
      Representation.span_range_eq_top_of_isIrreducible ρN

    have hz : ∀ m n : ↥N, (ρ (m : G) - 1) * (ρ (n : G) - (ψ n : K) • 1) = 0 := by
      intro m n
      apply eq_zero_of_forall_trace_mul_eq_zero
      intro x
      have hx : x ∈ Submodule.span K (Set.range ⇑ρN) := by rw [hspanN]; exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        rw [hρN]

        have e : ρ (g : G) * ((ρ (m : G) - 1) * (ρ (n : G) - (ψ n : K) • 1)) =
            ρ ((g * m * n : ↥N) : G) - (ψ n : K) • ρ ((g * m : ↥N) : G) - ρ ((g * n : ↥N) : G) +
              (ψ n : K) • ρ (g : G) := by
          simp only [Subgroup.coe_mul, map_mul, mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, mul_assoc,
            smul_sub]
          abel
        rw [e, map_add, map_sub, map_sub, map_smul, map_smul, htr _ (g * m * n).2, htr _ (g * m).2,
          htr _ (g * n).2, htr _ g.2]
        simp only [Subgroup.coe_mul, map_mul, Units.val_mul, smul_eq_mul]
        ring
      | zero => rw [zero_mul, map_zero]
      | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_mul_assoc, map_smul, hx, smul_zero]

    by_cases hscal : ∀ n : ↥N, ρ (n : G) = (ψ n : K) • 1
    ·
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hline ⟨v, hv, fun n hn => ⟨(ψ n : K), by rw [hscal ⟨n, hn⟩]; rfl⟩⟩
    · push Not at hscal
      obtain ⟨n₀, hn₀⟩ := hscal
      set f := ρ (n₀ : G) - (ψ n₀ : K) • 1 with hf
      have hf0 : f ≠ 0 := fun h => hn₀ (sub_eq_zero.mp h)

      have hfix : ∀ (m : ↥N) (y : V), ρ (m : G) (f y) = f y := by
        intro m y
        have := congrArg (fun h : Module.End K V => h y) (hz m n₀)
        simp only [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
          Module.End.one_apply] at this
        exact sub_eq_zero.mp this
      obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
        by_contra h
        push Not at h
        exact hf0 (LinearMap.ext h)
      exact hline ⟨f y, hy, fun n hn => ⟨1, by rw [one_smul]; exact hfix ⟨n, hn⟩ y⟩⟩

end Clifford

section Frobenius

open IsLocalRing

theorem eq_one_of_pow_eq_one_of_residue_eq_one {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {M : ℕ} (hM : IsUnit (M : A)) {η : A} (hη : η ^ M = 1) (hres : residue A η = 1) : η = 1 := by
  have hgeom : (∑ i ∈ Finset.range M, η ^ i) * (η - 1) = 0 := by rw [geom_sum_mul, hη, sub_self]
  have hunit : IsUnit (∑ i ∈ Finset.range M, η ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at hM ⊢
    rw [map_sum]
    simp_rw [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rwa [map_natCast] at hM
  rcases mul_eq_zero.mp hgeom with h | h
  · exact absurd h hunit.ne_zero
  · exact sub_eq_zero.mp h

theorem modEq_one_of_isFrobeniusAt_of_apply_eq {M : ℕ} [NeZero M] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ M) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : A.IsFrobeniusAt τ ℓ) (hfix : τ ζ = ζ) :
    ℓ ≡ 1 [MOD M] := by
  have hM0 : M ≠ 0 := NeZero.ne M

  have hζA : ζ ∈ A := by
    rcases A.mem_or_inv_mem ζ with h | h
    · exact h
    · have hζ1 : ζ ^ M = 1 := hζ.pow_eq_one
      have hζne : ζ ≠ 0 := hζ.ne_zero hM0
      have : ζ = (ζ⁻¹) ^ (M - 1) := by
        rw [inv_pow]
        refine (eq_inv_of_mul_eq_one_left ?_)
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM0), hζ1]
      rw [this]
      exact A.pow_mem h _
  set a : A := ⟨ζ, hζA⟩ with ha
  have haM : a ^ M = 1 := Subtype.ext (by rw [ha]; exact hζ.pow_eq_one)

  have hℓmax : ((ℓ : ℕ) : A) ∈ maximalIdeal A := by
    obtain ⟨hℓA, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := A)).mp hA
    have e : (⟨(ℓ : AlgebraicClosure ℚ), hℓA⟩ : A) = ((ℓ : ℕ) : A) := Subtype.ext (by simp)
    rwa [e] at hmax
  have hMunit : IsUnit ((M : ℕ) : A) := by
    by_contra hMu
    have hMmax : ((M : ℕ) : A) ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hMu
    have hcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM
    obtain ⟨x, y, hxy⟩ := (Nat.isCoprime_iff_coprime.mpr hcop : IsCoprime (ℓ : ℤ) (M : ℤ))
    have h1 : (1 : A) ∈ maximalIdeal A := by
      have : ((x : ℤ) : A) * (ℓ : A) + ((y : ℤ) : A) * (M : A) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : A)) hxy
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓmax) (Ideal.mul_mem_left _ _ hMmax)
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

  set abar := residue A a with habar
  have hτmem := hτ.mem_decompositionSubgroup
  have hsmul : ((⟨τ, hτmem⟩ : A.decompositionSubgroup ℚ) • a : A) = a := by
    apply Subtype.ext
    change τ • ζ = ζ
    rw [AlgEquiv.smul_def, hfix]
  have hfrob : abar ^ ℓ = abar := by
    rw [habar, ← hτ.smul_residue_eq (residue A a), ← IsLocalRing.ResidueField.residue_smul, hsmul]

  have habarM : abar ^ M = 1 := by rw [habar, ← map_pow, haM, map_one]
  have hprim : IsPrimitiveRoot abar M := by
    refine (IsPrimitiveRoot.iff_def abar M).mpr ⟨habarM, fun l hl => ?_⟩

    have h1 : a ^ l = 1 := by
      refine eq_one_of_pow_eq_one_of_residue_eq_one hMunit ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, haM, one_pow]
      · rw [map_pow, ← habar, hl]
    have h2 : ζ ^ l = 1 := by
      have := congrArg Subtype.val h1
      simpa [ha] using this
    exact hζ.dvd_of_pow_eq_one l h2

  have habar0 : abar ≠ 0 := hprim.ne_zero hM0
  have hpow : abar ^ (ℓ - 1) = 1 := by
    have h := hfrob
    rw [← Nat.sub_add_cancel hℓ.one_lt.le, pow_succ] at h
    nth_rw 3 [← one_mul abar] at h
    exact mul_right_cancel₀ habar0 h
  have hdvd : M ∣ ℓ - 1 := hprim.dvd_of_pow_eq_one _ hpow
  exact ((Nat.modEq_iff_dvd' hℓ.one_lt.le).mpr hdvd).symm

end Frobenius

section Assembly

variable {k : Type} [Field k]

local notation "Galℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped IntermediateField

theorem cheb_of_isOpen (H : Subgroup Galℚ) (hH : IsOpen ((H : Subgroup Galℚ) : Set Galℚ))
    (S : Finset ℕ) (σ : Galℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ g : Galℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H := by
  have hnhds : (H : Set Galℚ) ∈ nhds 1 := hH.mem_nhds H.one_mem
  obtain ⟨E, hEfin, hEnormal, hEH⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) H).mp hnhds
  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ E) = E.algebra := Subsingleton.elim _ _
  haveI hN : @Normal ℚ E _ _ DivisionRing.toRatAlgebra := by rw [halg]; exact hEnormal
  haveI hFD : @FiniteDimensional ℚ E _ _ DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hEfin
  haveI : NumberField E := @NumberField.mk _ _ inferInstance hFD
  haveI : IsGalois ℚ E := ⟨⟩
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker ≤ H := by
    intro x hx
    apply hEH
    haveI := hEnormal
    rw [← IntermediateField.restrictNormalHom_ker E, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hx
    convert hx
    rfl
  exact FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker E hker S σ

theorem isOpen_ker_rho (ρ : ResidualGaloisRep k) : IsOpen ((ρ.ρ.ker : Subgroup Galℚ) : Set Galℚ) := by
  obtain ⟨L, hL, hker⟩ := ρ.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hL
  apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) _ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ)

theorem main (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρ : ResidualGaloisRep k) (hirr : ρ.IsAbsolutelyIrreducible)
    (M : ℕ) [NeZero M] (S : Finset ℕ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ≡ 1 [MOD M] ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        LinearMap.trace k ρ.V (ρ.ρ σ) ≠ (ℓ : k) + 1 := by
  classical
  by_contra hcon
  have hcon' : ∀ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Galℚ),
      ℓ.Prime → ℓ ≡ 1 [MOD M] → ℓ ∉ S → A.LiesOverPrime ℓ → A.IsFrobeniusAt σ ℓ →
        LinearMap.trace k ρ.V (ρ.ρ σ) = (ℓ : k) + 1 := by
    intro ℓ A σ h1 h2 h3 h4 h5
    by_contra hne
    exact hcon ⟨ℓ, A, σ, h1, h2, h3, h4, h5, hne⟩

  obtain ⟨ψ, hψopen, -, hψfrob⟩ :=
    MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
      (k := k) p M (1 : (ZMod M)ˣ →* kˣ)

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) M
  set χM : Galℚ →* (ZMod M)ˣ := hζ.autToPow ℚ with hχM
  set N : Subgroup Galℚ := χM.ker with hN
  have hNfix : ∀ τ ∈ N, τ ζ = ζ := by
    intro τ hτ
    rw [hN, MonoidHom.mem_ker] at hτ
    have h := hζ.autToPow_spec ℚ τ
    rw [← hχM, hτ] at h
    rw [← h, Units.val_one, ZMod.val_one_eq_one_mod, hζ.eq_orderOf, pow_mod_orderOf, pow_one]
  have hcommN : ∀ a b : Galℚ, a * b * a⁻¹ * b⁻¹ ∈ N := by
    intro a b
    rw [hN, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm,
      mul_inv_cancel]
  have hNopen : IsOpen ((N : Subgroup Galℚ) : Set Galℚ) := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    apply Subgroup.isOpen_mono (H₁ := IntermediateField.fixingSubgroup ℚ⟮ζ⟯) _
      (IntermediateField.fixingSubgroup_isOpen ℚ⟮ζ⟯)
    intro σ hσ
    have hσζ : σ ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    rw [hN, MonoidHom.mem_ker]

    have h := hζ.autToPow_spec ℚ σ
    rw [hσζ, ← hχM] at h
    nth_rw 2 [← pow_one ζ] at h
    have hmod : (χM σ : ZMod M).val ≡ 1 [MOD M] := by
      rcases Nat.eq_zero_or_pos (χM σ : ZMod M).val with ha0 | hapos
      ·
        rw [ha0, pow_zero, pow_one] at h
        have hM1 : M = 1 := by rw [hζ.eq_orderOf, ← h, orderOf_one]
        rw [ha0, hM1]
        exact Nat.modEq_one
      · have h' : ζ ^ ((χM σ : ZMod M).val - 1) = 1 := by
          rw [← Nat.sub_add_cancel hapos, pow_succ, pow_one] at h
          exact mul_right_cancel₀ (hζ.ne_zero (NeZero.ne M)) (h.trans (one_mul ζ).symm)
        exact ((Nat.modEq_iff_dvd' hapos).mpr (hζ.dvd_of_pow_eq_one _ h')).symm
    apply Units.ext
    rw [Units.val_one]
    rw [← ZMod.natCast_zmod_val (χM σ : ZMod M)]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod, Nat.cast_one]

  have htrN : ∀ g ∈ N, LinearMap.trace k ρ.V (ρ.ρ g) = 1 + (ψ g : k) := by
    intro g hg
    set U : Subgroup Galℚ := ρ.ρ.ker ⊓ ψ.ker ⊓ N with hU
    have hUopen : IsOpen ((U : Subgroup Galℚ) : Set Galℚ) := by
      rw [hU, Subgroup.coe_inf, Subgroup.coe_inf]
      exact ((isOpen_ker_rho ρ).inter hψopen).inter hNopen
    obtain ⟨ℓ, A, τ, g₁, hℓ, hℓS₀, hA, hτ, hmem⟩ :=
      cheb_of_isOpen U hUopen (insert p (S ∪ M.primeFactors)) g
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact hℓS₀ (Finset.mem_insert_self _ _)
    have hℓM : ¬ ℓ ∣ M := fun h =>
      hℓS₀ (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hℓ, h, NeZero.ne M⟩)))
    have hℓS : ℓ ∉ S := fun h => hℓS₀ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))

    set h := g₁ * τ * g₁⁻¹ * g⁻¹ with hh
    have hmem' := hmem
    rw [hU, Subgroup.mem_inf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hmem'
    obtain ⟨⟨hh1, hh2⟩, hh3⟩ := hmem'

    have hτN : τ ∈ N := by
      have e : τ = g₁⁻¹ * (h * g) * g₁ := by rw [hh]; group
      rw [e]
      have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) (h * g) (N.mul_mem hh3 hg) g₁⁻¹
      rwa [inv_inv] at this
    have hℓ1 : ℓ ≡ 1 [MOD M] :=
      modEq_one_of_isFrobeniusAt_of_apply_eq hζ hℓ hℓM A hA τ hτ (hNfix τ hτN)

    have htrτ : LinearMap.trace k ρ.V (ρ.ρ τ) = (ℓ : k) + 1 := hcon' ℓ A τ hℓ hℓ1 hℓS hA hτ
    have hψτ : (ψ τ : k) = (ℓ : k) := by
      rw [hψfrob ℓ hℓ hℓM hℓp A hA τ hτ, MonoidHom.one_apply, Units.val_one, mul_one]
    have hρg : ρ.ρ g = ρ.ρ g₁ * ρ.ρ τ * ρ.ρ g₁⁻¹ := by
      have e : g = h⁻¹ * (g₁ * τ * g₁⁻¹) := by rw [hh]; group
      have hh1' : ρ.ρ h⁻¹ = 1 := by
        have hm := map_mul ρ.ρ h⁻¹ h
        rw [inv_mul_cancel, map_one, hh1, mul_one] at hm
        exact hm.symm
      rw [e, map_mul, hh1', one_mul, map_mul, map_mul]
    have htrg : LinearMap.trace k ρ.V (ρ.ρ g) = LinearMap.trace k ρ.V (ρ.ρ τ) := by
      rw [hρg, mul_assoc, LinearMap.trace_mul_comm, mul_assoc, ← map_mul, inv_mul_cancel, map_one,
        mul_one]
    have hψg : ψ g = ψ τ := by
      have e : g = h⁻¹ * (g₁ * τ * g₁⁻¹) := by rw [hh]; group
      rw [e, map_mul, map_inv, hh2, inv_one, one_mul, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    rw [htrg, htrτ, hψg, hψτ, add_comm]

  let K := AlgebraicClosure k
  let ρ' := ρ.baseChange K
  have h2 : (2 : K) ≠ 0 := by
    haveI : CharP K p := (Algebra.charP_iff k K p).mp inferInstance
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  let ψ' : Galℚ →* Kˣ := (Units.map (algebraMap k K : k →* K)).comp ψ
  have hρ' : ∀ g, ρ'.ρ g = (ρ.ρ g).baseChange K := fun g => rfl
  have htr' : ∀ g ∈ N, LinearMap.trace K ρ'.V (ρ'.ρ g) = 1 + (ψ' g : K) := by
    intro g hg
    rw [hρ']
    change LinearMap.trace K (TensorProduct k K ρ.V) ((ρ.ρ g).baseChange K) = _
    rw [LinearMap.trace_baseChange, htrN g hg, map_add, map_one]
    rfl
  haveI : N.Normal := by rw [hN]; infer_instance
  exact false_of_trace_eq_one_add h2 ρ'.ρ ρ'.finrank_eq hirr N hcommN ψ' htr'

end Assembly

end ResidualGaloisRep.NonEisenstein

theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (ρ : ResidualGaloisRep k) (hirr : ρ.IsAbsolutelyIrreducible)
    (M : ℕ) [NeZero M] (S : Finset ℕ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ≡ 1 [MOD M] ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
        LinearMap.trace k ρ.V (ρ.ρ σ) ≠ (ℓ : k) + 1 :=
  ResidualGaloisRep.NonEisenstein.main p hp2 ρ hirr M S

end S_ResidualGaloisRep_exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_ResidualGaloisRep_exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible (solution)
