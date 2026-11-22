-- Prove2me | solution 1 for QECCertificates.LRAT.buildPair_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:42.219202+00:00
-- url     : https://prove2.me/submissions/ea424a8d-6103-40ae-a30f-596e04fcbb7f

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Theorems.Thm_QECCertificates_LRAT_chainsFrom_complete
public import Theorems.Thm_QECCertificates_LRAT_prodFill_at
public import Theorems.Thm_QECCertificates_LRAT_prodFill_of_lt
public import Theorems.Thm_QECCertificates_LRAT_prodClauses_complete
public import Theorems.Thm_QECCertificates_LRAT_atMostK_complete
public import Theorems.Thm_QECCertificates_LRAT_xorChain_snd_ge
public import Theorems.Thm_QECCertificates_LRAT_chainsFrom_snd_ge
public import Theorems.Thm_QECCertificates_LRAT_chainsFrom_vars_lt
public import Theorems.Thm_QECCertificates_LRAT_prodClauses_vars_lt
public import Theorems.Thm_QECCertificates_LRAT_xorChain_vars_lt
public import Theorems.Thm_QECCertificates_LRAT_satFormula_of_agree
public import Theorems.Thm_QECCertificates_LRAT_xorChain_complete
public import Theorems.Thm_QECCertificates_LRAT_cntS_nil
public import Theorems.Thm_QECCertificates_LRAT_dotS_congr
public import Theorems.Thm_QECCertificates_LRAT_dotS_cons
public import Theorems.Thm_QECCertificates_LRAT_dotS_map
public import Theorems.Thm_QECCertificates_LRAT_dotS_nil
public import Theorems.Thm_QECCertificates_LRAT_satFormula_append
attribute [local simp] QECCertificates.LRAT.cntS_nil
attribute [local simp] QECCertificates.LRAT.dotS_cons
attribute [local simp] QECCertificates.LRAT.dotS_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {Rker Rpair : List (List Nat)} {n k : Nat} {σ : Assign}
    (hn : 0 < n) (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hcol₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hcol₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hwt : cntS σ (List.range n) ≤ k)
    (hker : ∀ r ∈ Rker, dotS σ r = false)
    (hpair : ∀ r ∈ Rpair, dotS (fun t => σ (n + t)) r = false)
    (hxw : dotS (fun t => σ t && σ (n + t)) (List.range n) = true) :
    ∃ τ : Assign, (∀ t, t < 2 * n → τ t = σ t) ∧
      SatFormula τ (buildPair Rker Rpair n k) := by
  have hge1 : 2 * n ≤ c1Of Rker n := chainsFrom_snd_ge Rker (2 * n)
  have hge2 : c1Of Rker n ≤ c2Of Rker Rpair n := chainsFrom_snd_ge Rpair (c1Of Rker n)
  have hge3 : c2Of Rker Rpair n + n ≤ c3Of Rker Rpair n := xorChain_snd_ge _ true _
  have hlt₁ : ∀ r ∈ Rker, ∀ t ∈ r, (fun j => j) t < 2 * n := fun r hr t ht => by
    have := hcol₁ r hr t ht
    change t < 2 * n
    omega
  obtain ⟨τ₁, hag₁, hcl₁⟩ :=
    chainsFrom_complete hne₁ (2 * n) σ hlt₁ (fun r hr => hker r hr)
  have hlt₂ : ∀ r ∈ Rpair, ∀ t ∈ r, (fun j => n + j) t < c1Of Rker n := fun r hr t ht => by
    have := hcol₂ r hr t ht
    change n + t < c1Of Rker n
    omega
  have hdot₂ : ∀ r ∈ Rpair, dotS (fun t => τ₁ (n + t)) r = false := by
    intro r hr
    have h := hpair r hr
    have hcongr : dotS (fun t => τ₁ (n + t)) r = dotS (fun t => σ (n + t)) r :=
      dotS_congr (fun t ht => hag₁ (n + t) (by have := hcol₂ r hr t ht; omega))
    rwa [hcongr]
  obtain ⟨τ₂, hag₂, hcl₂⟩ := chainsFrom_complete hne₂ (c1Of Rker n) τ₁ hlt₂ hdot₂
  have hprod : 2 * n ≤ c2Of Rker Rpair n := le_trans hge1 hge2
  have hcl₃ : ∀ C ∈ prodClauses (c2Of Rker Rpair n) n,
      SatClause (prodFill τ₂ (c2Of Rker Rpair n) n) C :=
    prodClauses_complete hprod
  have hag₃ : ∀ t, t < c2Of Rker Rpair n →
      prodFill τ₂ (c2Of Rker Rpair n) n t = τ₂ t :=
    fun _ ht => prodFill_of_lt ht
  have hprodvars_ne : prodVars Rker Rpair n ≠ [] := by
    intro h0
    have hlen := congrArg List.length h0
    simp [prodVars, List.length_map, List.length_range] at hlen
    omega
  have hlt₄ : ∀ t ∈ prodVars Rker Rpair n, t < c2Of Rker Rpair n + n := by
    intro t ht
    simp only [prodVars, List.mem_map, List.mem_range] at ht
    obtain ⟨j, hj, rfl⟩ := ht
    omega
  have hdot₄ : dotS (prodFill τ₂ (c2Of Rker Rpair n) n) (prodVars Rker Rpair n) = true := by
    have hmap : dotS (prodFill τ₂ (c2Of Rker Rpair n) n) (prodVars Rker Rpair n)
        = dotS (fun j => prodFill τ₂ (c2Of Rker Rpair n) n (c2Of Rker Rpair n + j))
            (List.range n) := by
      simp only [prodVars, dotS_map]
    rw [hmap]
    have hcongr : dotS (fun j => prodFill τ₂ (c2Of Rker Rpair n) n (c2Of Rker Rpair n + j))
          (List.range n)
        = dotS (fun j => σ j && σ (n + j)) (List.range n) := by
      refine dotS_congr (fun j hj => ?_)
      rw [prodFill_at _ _ _ j (List.mem_range.mp hj)]
      have hjn : j < n := List.mem_range.mp hj
      have hj2 : τ₂ j = σ j := by
        rw [hag₂ j (by omega)]
        exact hag₁ j (by omega)
      have hj3 : τ₂ (n + j) = σ (n + j) := by
        rw [hag₂ (n + j) (by omega)]
        exact hag₁ (n + j) (by omega)
      rw [hj2, hj3]
    rw [hcongr]
    exact hxw
  obtain ⟨τ₄, hag₄, hcl₄⟩ := xorChain_complete hprodvars_ne hlt₄ hdot₄
  have hagree₄ : ∀ t, t < 2 * n → τ₄ t = σ t := by
    intro t ht
    rw [hag₄ t (by omega), hag₃ t (by omega), hag₂ t (by omega)]
    exact hag₁ t ht
  have hwt₄ : cntS τ₄ (List.range n) ≤ k := by
    have hcongr : cntS τ₄ (List.range n) = cntS σ (List.range n) := by
      refine congrArg List.length ?_
      apply List.filter_congr
      intro a ha
      exact hagree₄ a (by have := List.mem_range.mp ha; omega)
    rw [hcongr]
    exact hwt
  have hlt₅ : ∀ t ∈ List.range n, t < c3Of Rker Rpair n := fun t ht => by
    have := List.mem_range.mp ht
    omega
  obtain ⟨τ₅, hag₅, hcl₅⟩ := atMostK_complete (k := k) (c := c3Of Rker Rpair n)
    (xs := List.range n) (σ := τ₄) hlt₅ hwt₄
  have e54 : ∀ t, t < c2Of Rker Rpair n + n → τ₅ t = τ₄ t :=
    fun t ht => hag₅ t (le_trans ht hge3)
  have e53 : ∀ t, t < c2Of Rker Rpair n + n →
      τ₅ t = prodFill τ₂ (c2Of Rker Rpair n) n t := by
    intro t ht
    rw [e54 t ht]
    exact hag₄ t ht
  have e52 : ∀ t, t < c2Of Rker Rpair n → τ₅ t = τ₂ t := by
    intro t ht
    rw [e53 t (by omega)]
    exact hag₃ t ht
  have e51 : ∀ t, t < c1Of Rker n → τ₅ t = τ₁ t := by
    intro t ht
    rw [e52 t (lt_of_lt_of_le ht hge2)]
    exact hag₂ t ht
  have hSeg1 : SatFormula τ₅ (kerClauses Rker n) := by
    refine satFormula_of_agree e51 ?_ hcl₁
    intro C hC l hl
    exact chainsFrom_vars_lt hne₁ hlt₁ C hC l hl
  have hSeg2 : SatFormula τ₅ (pairClauses Rker Rpair n) := by
    refine satFormula_of_agree e52 ?_ hcl₂
    intro C hC l hl
    exact chainsFrom_vars_lt hne₂ hlt₂ C hC l hl
  have hSeg3 : SatFormula τ₅ (prodClauses (c2Of Rker Rpair n) n) := by
    refine satFormula_of_agree e53 ?_ hcl₃
    intro C hC l hl
    exact prodClauses_vars_lt (by omega) C hC l hl
  have hSeg4 : SatFormula τ₅ (xwClauses Rker Rpair n) := by
    refine satFormula_of_agree hag₅ ?_ hcl₄
    intro C hC l hl
    exact xorChain_vars_lt hprodvars_ne hlt₄ C hC l hl
  refine ⟨τ₅, fun t ht => ?_, ?_⟩
  · rw [e51 t (lt_of_lt_of_le ht hge1)]
    exact hag₁ t ht
  · rw [buildPair]
    exact satFormula_append.mpr
      ⟨satFormula_append.mpr ⟨satFormula_append.mpr ⟨hSeg1, hSeg2⟩,
        satFormula_append.mpr ⟨hSeg3, hSeg4⟩⟩, hcl₅⟩
end QECCertificates.LRAT
