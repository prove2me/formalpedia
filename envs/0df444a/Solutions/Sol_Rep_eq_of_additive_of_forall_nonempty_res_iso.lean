-- Prove2me | solution 1 for Rep.eq_of_additive_of_forall_nonempty_res_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bed5eee7-3c25-52fa-a7e4-f069d9b43792

import Mathlib
import Theorems.Thm_Rep_exists_isIrreducible_forall_additive_eq_sum
import Theorems.Thm_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime
import Theorems.Thm_Rep_eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_eq_of_additive_of_forall_nonempty_res_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

namespace ArtIndDET

lemma shortExact_map_res {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (π : H →* G)
    (X : ShortComplex (Rep.{0} k G)) (hX : X.ShortExact) : (X.map (Rep.resFunctor π)).ShortExact := by
  have hinj : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hsurj : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hrk : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.map_of_exact (forget₂ (Rep k G) (ModuleCat k))).exact.moduleCat_range_eq_ker
  haveI : Mono (X.map (Rep.resFunctor π)).f := (Rep.mono_iff_injective _).2 fun a b h => hinj h
  haveI : Epi (X.map (Rep.resFunctor π)).g := (Rep.epi_iff_surjective _).2 fun b => hsurj b
  have hex : (X.map (Rep.resFunctor π)).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k H) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hrk
  exact ShortComplex.ShortExact.mk' hex inferInstance inferInstance

end ArtIndDET

open ArtIndDET in
theorem solution
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (ψ : Rep.{0} (ZMod p) G → ℤ)
    (hadd : ∀ (X : ShortComplex (Rep.{0} (ZMod p) G)), X.ShortExact →
      FiniteDimensional (ZMod p) X.X₂ → ψ X.X₂ = ψ X.X₁ + ψ X.X₃)
    (A B : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B]
    (h : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      Nonempty (Rep.res H.subtype A ≅ Rep.res H.subtype B)) :
    ψ A = ψ B := by
  obtain ⟨r, S, a, b, hS, hij, hφ⟩ := Rep.exists_isIrreducible_forall_additive_eq_sum A B
  haveI : ∀ i, FiniteDimensional (ZMod p) (S i) := fun i => (hS i).1

  have hn : ∀ H : Subgroup G, IsCyclic H → (Nat.card H).Coprime p →
      ∀ T : Rep.{0} (ZMod p) H, FiniteDimensional (ZMod p) T →
        ∑ i, ((a i : ℤ) - b i) * (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype (S i)) : ℤ) = 0 := by
    intro H hH hcop T hT
    haveI := hT
    let φ : Rep.{0} (ZMod p) G → ℤ := fun V => (Module.finrank (ZMod p) (T ⟶ Rep.res H.subtype V) : ℤ)
    have hφadd : ∀ X : ShortComplex (Rep.{0} (ZMod p) G), X.ShortExact → FiniteDimensional (ZMod p) X.X₂ →
        φ X.X₂ = φ X.X₁ + φ X.X₃ := by
      intro X hX hfin
      haveI : FiniteDimensional (ZMod p) (X.map (Rep.resFunctor H.subtype)).X₂ := hfin
      have := Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime hcop T (X.map (Rep.resFunctor H.subtype))
        (shortExact_map_res H.subtype X hX)
      simp only [φ]
      exact_mod_cast this
    obtain ⟨hA, hB⟩ := hφ φ hφadd
    obtain ⟨e⟩ := h H hH hcop
    have hAB : φ A = φ B := by
      simp only [φ]
      exact_mod_cast (Linear.homCongr (ZMod p) (Iso.refl T) e).finrank_eq
    rw [hA, hB] at hAB
    have : ∑ i, ((a i : ℤ) - b i) * φ (S i) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, hAB, sub_self]
    simpa only [φ] using this
  have hzero := Rep.eq_zero_of_forall_sum_mul_finrank_hom_res_eq_zero S (fun i => (hS i).2) hij
    (fun i => (a i : ℤ) - b i) hn
  have hab : ∀ i, (a i : ℤ) = b i := fun i => sub_eq_zero.1 (congrFun hzero i)
  obtain ⟨hA, hB⟩ := hφ ψ hadd
  rw [hA, hB]
  exact Finset.sum_congr rfl fun i _ => by rw [hab i]

end S_Rep_eq_of_additive_of_forall_nonempty_res_iso
end P2MW
export P2MW.S_Rep_eq_of_additive_of_forall_nonempty_res_iso (solution)
