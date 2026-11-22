-- Prove2me | solution 1 for QECCertificates.LRAT.chainsFrom_vars_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:05.716118+00:00
-- url     : https://prove2.me/submissions/f3fe1fc6-1475-4949-a027-fc778fb98d55

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_snd
public import Theorems.Thm_QECCertificates_LRAT_xorChainAux_vars_lt
public import Theorems.Thm_QECCertificates_LRAT_xorChain_snd_ge
public import Theorems.Thm_QECCertificates_LRAT_chainsFrom_snd_ge
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {f : Nat → Nat} {rows : List (List Nat)} {c : Nat}
    (hne : ∀ r ∈ rows, r ≠ [])
    (hlt : ∀ r ∈ rows, ∀ t ∈ r, f t < c) :
    ∀ C ∈ (chainsFrom f rows c).1, ∀ l ∈ C, l.1 < (chainsFrom f rows c).2 := by
  induction rows generalizing c with
  | nil => intro C hC; simp only [chainsFrom, List.not_mem_nil] at hC
  | cons r₀ rest ih =>
      intro C hC
      have hr₀ : r₀ ≠ [] := hne r₀ (List.mem_cons_self ..)
      have hmap_ne : r₀.map f ≠ [] := fun h0 => hr₀ (List.map_eq_nil_iff.mp h0)
      obtain ⟨x₀, t, hmap⟩ : ∃ x₀ t, r₀.map f = x₀ :: t := by
        cases hm : r₀.map f with
        | nil => exact absurd hm hmap_ne
        | cons x₀ t => exact ⟨x₀, t, rfl⟩
      have hchain : xorChain (r₀.map f) false c = xorChainAux t false x₀ c := by
        simp only [xorChain, hmap]
      have hc' : (xorChain (r₀.map f) false c).2 = c + t.length := by
        rw [hchain, xorChainAux_snd]
      have hx₀ : x₀ < c := by
        obtain ⟨s, hs, hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_self ..)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s hs
      have ht : ∀ s ∈ t, s < c := by
        intro s hs
        obtain ⟨s', hs', hsf⟩ := List.mem_map.mp (by rw [hmap]; exact List.mem_cons_of_mem _ hs)
        rw [← hsf]
        exact hlt r₀ (List.mem_cons_self ..) s' hs'
      have hc'' : (xorChainAux t false x₀ c).2 = c + t.length := by
        rw [← hchain]; exact hc'
      simp only [chainsFrom, List.mem_append] at hC
      rcases hC with hC | hC
      · rw [hchain] at hC
        intro l hl
        have h1 := xorChainAux_vars_lt t false x₀ c hx₀ ht C hC l hl
        exact lt_of_lt_of_le h1 (by
          have h2 := chainsFrom_snd_ge (f := f) rest ((xorChain (r₀.map f) false c).2)
          simp only [chainsFrom]
          omega)
      · intro l hl
        have := ih (fun r hr => hne r (List.mem_cons_of_mem _ hr)) (fun r hr s hs =>
          lt_of_lt_of_le (hlt r (List.mem_cons_of_mem _ hr) s hs) (xorChain_snd_ge _ false c))
          C hC l hl
        simpa only [chainsFrom] using this
end QECCertificates.LRAT
